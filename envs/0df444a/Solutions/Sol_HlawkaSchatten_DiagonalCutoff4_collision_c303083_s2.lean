-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303083_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:59:28.585048+00:00
-- url     : https://prove2.me/submissions/aefb40d5-2be2-46a7-b9df-85241e6c5b2c

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
/- Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa,
bwdaugherty and Yuxuan Xu. All new numerical implications are checked below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring
theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]
end HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

theorem power_ratio_upper {x y : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^m ≤ y^n) :
    x^((m : ℝ)/(n : ℝ)) ≤ y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.rpow_le_rpow (pow_nonneg hx m) h (one_div_nonneg.mpr hn0.le)
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast y n,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_one_div_cancel hn0.ne', Real.rpow_one] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem norm_support_interval {p b : ℝ} (hp : 1 < p) (hb : 1 < b)
    (hpb : p ≤ b) (w x : Fin 3 → ℝ)
    (hw1 : ∀ i, |w i| ≤ 1)
    (hw : (∑ i, |w i|^(b/(b-1))) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have hqp : b/(b-1) ≤ p/(p-1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hq0 : 0 ≤ b/(b-1) := div_nonneg (by linarith) (by linarith)
  apply norm_support (q := p/(p-1))
    ((Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl)
  apply le_trans _ hw
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg _) (hw1 i) hq0 hqp

theorem norm_support_interval_cert {p b : ℝ} (m n : ℕ) (hn : 0 < n)
    (hp : 1 < p) (hb : 1 < b) (hpb : p ≤ b)
    (hconj : b/(b-1) = (m : ℝ)/(n : ℝ))
    (w v x : Fin 3 → ℝ) (hw1 : ∀ i, |w i| ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (hpowers : ∀ i, |w i|^m ≤ (v i)^n) (hs : (∑ i, v i) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  apply norm_support_interval hp hb hpb w x hw1
  rw [hconj]
  exact (Finset.sum_le_sum fun i _ =>
    power_ratio_upper m n hn (abs_nonneg _) (hv i) (hpowers i)).trans hs

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6




theorem total_eq (X : Fin 3 → Fin 3 → ℝ) : total X = X 0+X 1+X 2 := by
  simp [total,Fin.sum_univ_three]
theorem pair0 (X : Fin 3 → Fin 3 → ℝ) : pair X 0 = X 1+X 2 := by
  rw [pair,total_eq];abel
theorem pair1 (X : Fin 3 → Fin 3 → ℝ) : pair X 1 = X 0+X 2 := by
  rw [pair,total_eq];abel
theorem pair2 (X : Fin 3 → Fin 3 → ℝ) : pair X 2 = X 0+X 1 := by
  rw [pair,total_eq];abel


theorem oriented_frame {p q k d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : RelativeOrientedData p q k d X) : Frame p k (3*q) d X := by
  constructor
  · simpa [Fin.sum_univ_three] using h.sum
  · simpa [total_eq] using h.norm_le_total
  · simpa [total_eq] using h.total_one
  · simpa [total_eq] using h.total_cap.le
  · intro i;fin_cases i
    · simpa [pair0] using h.main0
    · simpa [pair1] using h.main1
    · simpa [pair2] using h.main2
  · intro i h';fin_cases i
    · simpa [pair0] using h.max0 h'
    · simpa [pair1] using h.max1 h'
    · simpa [pair2] using h.max2 h'
  · simpa [total_eq,Fin.sum_univ_three,pair0,pair1,pair2] using h.linear_failure

theorem total_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) :
    total (relabel e X) = total X ∘ e := by
  ext h
  simp only [total,Finset.sum_apply,relabel,Function.comp_apply]
  exact Equiv.sum_comp e (fun j => X j (e h))

theorem pair_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    pair (relabel e X) i = pair X (e i) ∘ e := by
  ext h
  simp [pair,total_relabel,relabel]

theorem frame_relabel {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : Frame p k A d X) (e : Equiv.Perm (Fin 3)) : Frame p k A d (relabel e X) := by
  have hr (j : Fin 3) : lpNorm p (relabel e X j) = lpNorm p (X (e j)) :=
    lpNorm_comp_equiv p (X (e j)) e
  have ht : lpNorm p (total (relabel e X)) = lpNorm p (total X) := by
    rw [total_relabel,lpNorm_comp_equiv]
  have hp (i : Fin 3) : lpNorm p (pair (relabel e X) i) = lpNorm p (pair X (e i)) := by
    rw [pair_relabel,lpNorm_comp_equiv]
  constructor
  · simp_rw [hr];rw [Equiv.sum_comp e (fun j => lpNorm p (X j))];exact h.sum
  · intro j;rw [hr,ht];exact h.row_total (e j)
  · rw [ht];exact h.total_one
  · rw [ht];exact h.total_cap
  · intro i;rw [hp,pair_relabel];exact h.main (e i)
  · intro i j;rw [pair_relabel];exact h.maximal (e i) (e j)
  · simp_rw [ht,hp];rw [Equiv.sum_comp e (fun i => lpNorm p (pair X i))];exact h.linear_failure

theorem frame_box_of_base {p k A d ell u v w rho : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_ratio_of_base {p k A d rho R : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201

end HlawkaSchatten.DiagonalCutoff6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6


theorem pair_eq_of_distinct (X : Fin 3 → Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : pair X i = X j+X l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
  all_goals first
    | exact pair0 X
    | exact (pair0 X).trans (add_comm _ _)
    | exact pair1 X
    | exact (pair1 X).trans (add_comm _ _)
    | exact pair2 X
    | exact (pair2 X).trans (add_comm _ _)

theorem frame_linear_data {p k A d : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : Frame p k A d X) :
    LinearData k A d X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · exact h.main
  · exact h.maximal
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem linear_data_bounds {k A d T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : LinearData k A d X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]

theorem positive_pair_majorant {p a rho alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hc1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hc2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ pair X i i)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ pair X i i+alpha*(pair X i j+pair X i l) := by
  rw [HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p _ hij hil hjl]
  have hh := signed_majorant hp ha hap hrho hrho1 halpha hc1 hc2 (hm i)
    (hratio i j hij) (hratio i l hil)
  simpa only [abs_of_nonneg (hsign i j hij),abs_of_nonneg (hsign i l hil)] using hh

theorem frame_weaken {p k A d k' A' d' : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (h : Frame p k A d X) (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    Frame p k' A' d' X := by
  have f := frame_linear_data hp X h
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  constructor
  · exact h.sum
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap.trans hA
  · intro i
    exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (h.main i)
  · exact h.maximal
  · have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
    linarith only [hh,h.linear_failure]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c303083_s2_s2_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1193494731/5000000000 : ℝ)*x 0 + (1005320361/2000000000 : ℝ)*x 1 + (1355442553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1193494731/5000000000 : ℝ)^33 ≤ (15092551353527/100000000000000 : ℝ)^25 := by
    have hnat : (1193494731 : ℕ)^33*100000000000000^25 ≤ 15092551353527^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193494731 5000000000 15092551353527 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005320361/2000000000 : ℝ)^33 ≤ (10083755945999/25000000000000 : ℝ)^25 := by
    have hnat : (1005320361 : ℕ)^33*25000000000000^25 ≤ 10083755945999^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005320361 2000000000 10083755945999 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355442553/2500000000 : ℝ)^33 ≤ (8914484970687/20000000000000 : ℝ)^25 := by
    have hnat : (1355442553 : ℕ)^33*20000000000000^25 ≤ 8914484970687^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355442553 2500000000 8914484970687 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1193494731/5000000000 : ℝ), (1005320361/2000000000 : ℝ), (1355442553/2500000000 : ℝ)] ![(15092551353527/100000000000000 : ℝ), (10083755945999/25000000000000 : ℝ), (8914484970687/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1193494731/5000000000 : ℝ)|^33 ≤ (15092551353527/100000000000000 : ℝ)^25
        have hw : |(-1193494731/5000000000 : ℝ)|=(1193494731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005320361/2000000000 : ℝ)|^33 ≤ (10083755945999/25000000000000 : ℝ)^25
        have hw : |(1005320361/2000000000 : ℝ)|=(1005320361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355442553/2500000000 : ℝ)|^33 ≤ (8914484970687/20000000000000 : ℝ)^25
        have hw : |(1355442553/2500000000 : ℝ)|=(1355442553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1741834809/2500000000 : ℝ)*x 0 + (-95868923/1000000000 : ℝ)*x 1 + (4357906841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1741834809/2500000000 : ℝ)^33 ≤ (15516307985981/25000000000000 : ℝ)^25 := by
    have hnat : (1741834809 : ℕ)^33*25000000000000^25 ≤ 15516307985981^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741834809 2500000000 15516307985981 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95868923/1000000000 : ℝ)^33 ≤ (4527044463151/100000000000000 : ℝ)^25 := by
    have hnat : (95868923 : ℕ)^33*100000000000000^25 ≤ 4527044463151^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95868923 1000000000 4527044463151 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4357906841/10000000000 : ℝ)^33 ≤ (16703861788991/50000000000000 : ℝ)^25 := by
    have hnat : (4357906841 : ℕ)^33*50000000000000^25 ≤ 16703861788991^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357906841 10000000000 16703861788991 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1741834809/2500000000 : ℝ), (-95868923/1000000000 : ℝ), (4357906841/10000000000 : ℝ)] ![(15516307985981/25000000000000 : ℝ), (4527044463151/100000000000000 : ℝ), (16703861788991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1741834809/2500000000 : ℝ)|^33 ≤ (15516307985981/25000000000000 : ℝ)^25
        have hw : |(1741834809/2500000000 : ℝ)|=(1741834809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-95868923/1000000000 : ℝ)|^33 ≤ (4527044463151/100000000000000 : ℝ)^25
        have hw : |(-95868923/1000000000 : ℝ)|=(95868923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4357906841/10000000000 : ℝ)|^33 ≤ (16703861788991/50000000000000 : ℝ)^25
        have hw : |(4357906841/10000000000 : ℝ)|=(4357906841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3790781411/10000000000 : ℝ)*x 0 + (6447785219/10000000000 : ℝ)*x 1 + (-1257952919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3790781411/10000000000 : ℝ)^33 ≤ (27792136864511/100000000000000 : ℝ)^25 := by
    have hnat : (3790781411 : ℕ)^33*100000000000000^25 ≤ 27792136864511^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3790781411 10000000000 27792136864511 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6447785219/10000000000 : ℝ)^33 ≤ (28015085137183/50000000000000 : ℝ)^25 := by
    have hnat : (6447785219 : ℕ)^33*50000000000000^25 ≤ 28015085137183^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6447785219 10000000000 28015085137183 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1257952919/5000000000 : ℝ)^33 ≤ (8088846420589/50000000000000 : ℝ)^25 := by
    have hnat : (1257952919 : ℕ)^33*50000000000000^25 ≤ 8088846420589^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257952919 5000000000 8088846420589 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3790781411/10000000000 : ℝ), (6447785219/10000000000 : ℝ), (-1257952919/5000000000 : ℝ)] ![(27792136864511/100000000000000 : ℝ), (28015085137183/50000000000000 : ℝ), (8088846420589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3790781411/10000000000 : ℝ)|^33 ≤ (27792136864511/100000000000000 : ℝ)^25
        have hw : |(3790781411/10000000000 : ℝ)|=(3790781411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6447785219/10000000000 : ℝ)|^33 ≤ (28015085137183/50000000000000 : ℝ)^25
        have hw : |(6447785219/10000000000 : ℝ)|=(6447785219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1257952919/5000000000 : ℝ)|^33 ≤ (8088846420589/50000000000000 : ℝ)^25
        have hw : |(-1257952919/5000000000 : ℝ)|=(1257952919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2355829517/10000000000 : ℝ)*x 0 + (4997615423/10000000000 : ℝ)*x 1 + (5473872127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2355829517/10000000000 : ℝ)^33 ≤ (7416515318717/50000000000000 : ℝ)^25 := by
    have hnat : (2355829517 : ℕ)^33*50000000000000^25 ≤ 7416515318717^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2355829517 10000000000 7416515318717 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4997615423/10000000000 : ℝ)^33 ≤ (4002828099471/10000000000000 : ℝ)^25 := by
    have hnat : (4997615423 : ℕ)^33*10000000000000^25 ≤ 4002828099471^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997615423 10000000000 4002828099471 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473872127/10000000000 : ℝ)^33 ≤ (45138688350687/100000000000000 : ℝ)^25 := by
    have hnat : (5473872127 : ℕ)^33*100000000000000^25 ≤ 45138688350687^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473872127 10000000000 45138688350687 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2355829517/10000000000 : ℝ), (4997615423/10000000000 : ℝ), (5473872127/10000000000 : ℝ)] ![(7416515318717/50000000000000 : ℝ), (4002828099471/10000000000000 : ℝ), (45138688350687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2355829517/10000000000 : ℝ)|^33 ≤ (7416515318717/50000000000000 : ℝ)^25
        have hw : |(-2355829517/10000000000 : ℝ)|=(2355829517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4997615423/10000000000 : ℝ)|^33 ≤ (4002828099471/10000000000000 : ℝ)^25
        have hw : |(4997615423/10000000000 : ℝ)|=(4997615423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473872127/10000000000 : ℝ)|^33 ≤ (45138688350687/100000000000000 : ℝ)^25
        have hw : |(5473872127/10000000000 : ℝ)|=(5473872127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6479520607/10000000000 : ℝ)*x 0 + (-2698361/10000000000 : ℝ)*x 1 + (2666126067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6479520607/10000000000 : ℝ)^33 ≤ (2819723993799/5000000000000 : ℝ)^25 := by
    have hnat : (6479520607 : ℕ)^33*5000000000000^25 ≤ 2819723993799^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6479520607 10000000000 2819723993799 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698361/10000000000 : ℝ)^33 ≤ (972796663/50000000000000 : ℝ)^25 := by
    have hnat : (2698361 : ℕ)^33*50000000000000^25 ≤ 972796663^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698361 10000000000 972796663 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2666126067/5000000000 : ℝ)^33 ≤ (5450446816033/12500000000000 : ℝ)^25 := by
    have hnat : (2666126067 : ℕ)^33*12500000000000^25 ≤ 5450446816033^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666126067 5000000000 5450446816033 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6479520607/10000000000 : ℝ), (-2698361/10000000000 : ℝ), (2666126067/5000000000 : ℝ)] ![(2819723993799/5000000000000 : ℝ), (972796663/50000000000000 : ℝ), (5450446816033/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6479520607/10000000000 : ℝ)|^33 ≤ (2819723993799/5000000000000 : ℝ)^25
        have hw : |(6479520607/10000000000 : ℝ)|=(6479520607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2698361/10000000000 : ℝ)|^33 ≤ (972796663/50000000000000 : ℝ)^25
        have hw : |(-2698361/10000000000 : ℝ)|=(2698361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2666126067/5000000000 : ℝ)|^33 ≤ (5450446816033/12500000000000 : ℝ)^25
        have hw : |(2666126067/5000000000 : ℝ)|=(2666126067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (778326823/2500000000 : ℝ)*x 0 + (7574162597/10000000000 : ℝ)*x 1 + (-165004547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (778326823/2500000000 : ℝ)^33 ≤ (5357880634649/25000000000000 : ℝ)^25 := by
    have hnat : (778326823 : ℕ)^33*25000000000000^25 ≤ 5357880634649^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778326823 2500000000 5357880634649 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7574162597/10000000000 : ℝ)^33 ≤ (1732454001219/2500000000000 : ℝ)^25 := by
    have hnat : (7574162597 : ℕ)^33*2500000000000^25 ≤ 1732454001219^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7574162597 10000000000 1732454001219 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165004547/1000000000 : ℝ)^33 ≤ (579394837677/6250000000000 : ℝ)^25 := by
    have hnat : (165004547 : ℕ)^33*6250000000000^25 ≤ 579394837677^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165004547 1000000000 579394837677 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(778326823/2500000000 : ℝ), (7574162597/10000000000 : ℝ), (-165004547/1000000000 : ℝ)] ![(5357880634649/25000000000000 : ℝ), (1732454001219/2500000000000 : ℝ), (579394837677/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(778326823/2500000000 : ℝ)|^33 ≤ (5357880634649/25000000000000 : ℝ)^25
        have hw : |(778326823/2500000000 : ℝ)|=(778326823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7574162597/10000000000 : ℝ)|^33 ≤ (1732454001219/2500000000000 : ℝ)^25
        have hw : |(7574162597/10000000000 : ℝ)|=(7574162597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-165004547/1000000000 : ℝ)|^33 ≤ (579394837677/6250000000000 : ℝ)^25
        have hw : |(-165004547/1000000000 : ℝ)|=(165004547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3063110179/10000000000 : ℝ)*x 0 + (965880939/2000000000 : ℝ)*x 1 + (5067039903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3063110179/10000000000 : ℝ)^33 ≤ (20976578730977/100000000000000 : ℝ)^25 := by
    have hnat : (3063110179 : ℕ)^33*100000000000000^25 ≤ 20976578730977^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3063110179 10000000000 20976578730977 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965880939/2000000000 : ℝ)^33 ≤ (19129761535791/50000000000000 : ℝ)^25 := by
    have hnat : (965880939 : ℕ)^33*50000000000000^25 ≤ 19129761535791^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965880939 2000000000 19129761535791 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5067039903/10000000000 : ℝ)^33 ≤ (8152779636761/20000000000000 : ℝ)^25 := by
    have hnat : (5067039903 : ℕ)^33*20000000000000^25 ≤ 8152779636761^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5067039903 10000000000 8152779636761 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3063110179/10000000000 : ℝ), (965880939/2000000000 : ℝ), (5067039903/10000000000 : ℝ)] ![(20976578730977/100000000000000 : ℝ), (19129761535791/50000000000000 : ℝ), (8152779636761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3063110179/10000000000 : ℝ)|^33 ≤ (20976578730977/100000000000000 : ℝ)^25
        have hw : |(3063110179/10000000000 : ℝ)|=(3063110179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(965880939/2000000000 : ℝ)|^33 ≤ (19129761535791/50000000000000 : ℝ)^25
        have hw : |(965880939/2000000000 : ℝ)|=(965880939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5067039903/10000000000 : ℝ)|^33 ≤ (8152779636761/20000000000000 : ℝ)^25
        have hw : |(5067039903/10000000000 : ℝ)|=(5067039903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1279490961/10000000000 : ℝ)*x 0 + (3661137817/10000000000 : ℝ)*x 1 + (7368816263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1279490961/10000000000 : ℝ)^33 ≤ (6626575236969/100000000000000 : ℝ)^25 := by
    have hnat : (1279490961 : ℕ)^33*100000000000000^25 ≤ 6626575236969^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279490961 10000000000 6626575236969 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3661137817/10000000000 : ℝ)^33 ≤ (5308883777931/20000000000000 : ℝ)^25 := by
    have hnat : (3661137817 : ℕ)^33*20000000000000^25 ≤ 5308883777931^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3661137817 10000000000 5308883777931 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7368816263/10000000000 : ℝ)^33 ≤ (33414502931297/50000000000000 : ℝ)^25 := by
    have hnat : (7368816263 : ℕ)^33*50000000000000^25 ≤ 33414502931297^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7368816263 10000000000 33414502931297 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1279490961/10000000000 : ℝ), (3661137817/10000000000 : ℝ), (7368816263/10000000000 : ℝ)] ![(6626575236969/100000000000000 : ℝ), (5308883777931/20000000000000 : ℝ), (33414502931297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1279490961/10000000000 : ℝ)|^33 ≤ (6626575236969/100000000000000 : ℝ)^25
        have hw : |(-1279490961/10000000000 : ℝ)|=(1279490961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3661137817/10000000000 : ℝ)|^33 ≤ (5308883777931/20000000000000 : ℝ)^25
        have hw : |(3661137817/10000000000 : ℝ)|=(3661137817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7368816263/10000000000 : ℝ)|^33 ≤ (33414502931297/50000000000000 : ℝ)^25
        have hw : |(7368816263/10000000000 : ℝ)|=(7368816263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1660597233/2000000000 : ℝ)*x 0 + (-28530671/500000000 : ℝ)*x 1 + (2896619157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1660597233/2000000000 : ℝ)^33 ≤ (78232875774867/100000000000000 : ℝ)^25 := by
    have hnat : (1660597233 : ℕ)^33*100000000000000^25 ≤ 78232875774867^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660597233 2000000000 78232875774867 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28530671/500000000 : ℝ)^33 ≤ (570573272639/25000000000000 : ℝ)^25 := by
    have hnat : (28530671 : ℕ)^33*25000000000000^25 ≤ 570573272639^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28530671 500000000 570573272639 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2896619157/10000000000 : ℝ)^33 ≤ (19484831126131/100000000000000 : ℝ)^25 := by
    have hnat : (2896619157 : ℕ)^33*100000000000000^25 ≤ 19484831126131^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2896619157 10000000000 19484831126131 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1660597233/2000000000 : ℝ), (-28530671/500000000 : ℝ), (2896619157/10000000000 : ℝ)] ![(78232875774867/100000000000000 : ℝ), (570573272639/25000000000000 : ℝ), (19484831126131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1660597233/2000000000 : ℝ)|^33 ≤ (78232875774867/100000000000000 : ℝ)^25
        have hw : |(1660597233/2000000000 : ℝ)|=(1660597233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28530671/500000000 : ℝ)|^33 ≤ (570573272639/25000000000000 : ℝ)^25
        have hw : |(-28530671/500000000 : ℝ)|=(28530671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2896619157/10000000000 : ℝ)|^33 ≤ (19484831126131/100000000000000 : ℝ)^25
        have hw : |(2896619157/10000000000 : ℝ)|=(2896619157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4057300427/10000000000 : ℝ)*x 0 + (861071841/1250000000 : ℝ)*x 1 + (-192434969/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4057300427/10000000000 : ℝ)^33 ≤ (3039996334923/10000000000000 : ℝ)^25 := by
    have hnat : (4057300427 : ℕ)^33*10000000000000^25 ≤ 3039996334923^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4057300427 10000000000 3039996334923 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861071841/1250000000 : ℝ)^33 ≤ (30570375838949/50000000000000 : ℝ)^25 := by
    have hnat : (861071841 : ℕ)^33*50000000000000^25 ≤ 30570375838949^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861071841 1250000000 30570375838949 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192434969/1250000000 : ℝ)^33 ≤ (528705310407/6250000000000 : ℝ)^25 := by
    have hnat : (192434969 : ℕ)^33*6250000000000^25 ≤ 528705310407^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192434969 1250000000 528705310407 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4057300427/10000000000 : ℝ), (861071841/1250000000 : ℝ), (-192434969/1250000000 : ℝ)] ![(3039996334923/10000000000000 : ℝ), (30570375838949/50000000000000 : ℝ), (528705310407/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4057300427/10000000000 : ℝ)|^33 ≤ (3039996334923/10000000000000 : ℝ)^25
        have hw : |(4057300427/10000000000 : ℝ)|=(4057300427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(861071841/1250000000 : ℝ)|^33 ≤ (30570375838949/50000000000000 : ℝ)^25
        have hw : |(861071841/1250000000 : ℝ)|=(861071841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-192434969/1250000000 : ℝ)|^33 ≤ (528705310407/6250000000000 : ℝ)^25
        have hw : |(-192434969/1250000000 : ℝ)|=(192434969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1344935129/5000000000 : ℝ)*x 0 + (465305929/1250000000 : ℝ)*x 1 + (6375009101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344935129/5000000000 : ℝ)^33 ≤ (3534071690461/20000000000000 : ℝ)^25 := by
    have hnat : (1344935129 : ℕ)^33*20000000000000^25 ≤ 3534071690461^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344935129 5000000000 3534071690461 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465305929/1250000000 : ℝ)^33 ≤ (6783185994763/25000000000000 : ℝ)^25 := by
    have hnat : (465305929 : ℕ)^33*25000000000000^25 ≤ 6783185994763^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465305929 1250000000 6783185994763 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6375009101/10000000000 : ℝ)^33 ≤ (27598448773799/50000000000000 : ℝ)^25 := by
    have hnat : (6375009101 : ℕ)^33*50000000000000^25 ≤ 27598448773799^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6375009101 10000000000 27598448773799 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344935129/5000000000 : ℝ), (465305929/1250000000 : ℝ), (6375009101/10000000000 : ℝ)] ![(3534071690461/20000000000000 : ℝ), (6783185994763/25000000000000 : ℝ), (27598448773799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344935129/5000000000 : ℝ)|^33 ≤ (3534071690461/20000000000000 : ℝ)^25
        have hw : |(1344935129/5000000000 : ℝ)|=(1344935129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(465305929/1250000000 : ℝ)|^33 ≤ (6783185994763/25000000000000 : ℝ)^25
        have hw : |(465305929/1250000000 : ℝ)|=(465305929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6375009101/10000000000 : ℝ)|^33 ≤ (27598448773799/50000000000000 : ℝ)^25
        have hw : |(6375009101/10000000000 : ℝ)|=(6375009101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-888294413/5000000000 : ℝ)*x 0 + (115317211/200000000 : ℝ)*x 1 + (2565108271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (888294413/5000000000 : ℝ)^33 ≤ (10220090526153/100000000000000 : ℝ)^25 := by
    have hnat : (888294413 : ℕ)^33*100000000000000^25 ≤ 10220090526153^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888294413 5000000000 10220090526153 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115317211/200000000 : ℝ)^33 ≤ (24171892935647/50000000000000 : ℝ)^25 := by
    have hnat : (115317211 : ℕ)^33*50000000000000^25 ≤ 24171892935647^25*200000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115317211 200000000 24171892935647 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565108271/5000000000 : ℝ)^33 ≤ (4143612357869/10000000000000 : ℝ)^25 := by
    have hnat : (2565108271 : ℕ)^33*10000000000000^25 ≤ 4143612357869^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565108271 5000000000 4143612357869 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-888294413/5000000000 : ℝ), (115317211/200000000 : ℝ), (2565108271/5000000000 : ℝ)] ![(10220090526153/100000000000000 : ℝ), (24171892935647/50000000000000 : ℝ), (4143612357869/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-888294413/5000000000 : ℝ)|^33 ≤ (10220090526153/100000000000000 : ℝ)^25
        have hw : |(-888294413/5000000000 : ℝ)|=(888294413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(115317211/200000000 : ℝ)|^33 ≤ (24171892935647/50000000000000 : ℝ)^25
        have hw : |(115317211/200000000 : ℝ)|=(115317211/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2565108271/5000000000 : ℝ)|^33 ≤ (4143612357869/10000000000000 : ℝ)^25
        have hw : |(2565108271/5000000000 : ℝ)|=(2565108271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (980039481/1250000000 : ℝ)*x 0 + (-19069941/10000000000 : ℝ)*x 1 + (1877368973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980039481/1250000000 : ℝ)^33 ≤ (1813260938713/2500000000000 : ℝ)^25 := by
    have hnat : (980039481 : ℕ)^33*2500000000000^25 ≤ 1813260938713^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980039481 1250000000 1813260938713 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19069941/10000000000 : ℝ)^33 ≤ (25707576759/100000000000000 : ℝ)^25 := by
    have hnat : (19069941 : ℕ)^33*100000000000000^25 ≤ 25707576759^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19069941 10000000000 25707576759 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1877368973/5000000000 : ℝ)^33 ≤ (1715240928919/6250000000000 : ℝ)^25 := by
    have hnat : (1877368973 : ℕ)^33*6250000000000^25 ≤ 1715240928919^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877368973 5000000000 1715240928919 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(980039481/1250000000 : ℝ), (-19069941/10000000000 : ℝ), (1877368973/5000000000 : ℝ)] ![(1813260938713/2500000000000 : ℝ), (25707576759/100000000000000 : ℝ), (1715240928919/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(980039481/1250000000 : ℝ)|^33 ≤ (1813260938713/2500000000000 : ℝ)^25
        have hw : |(980039481/1250000000 : ℝ)|=(980039481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19069941/10000000000 : ℝ)|^33 ≤ (25707576759/100000000000000 : ℝ)^25
        have hw : |(-19069941/10000000000 : ℝ)|=(19069941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1877368973/5000000000 : ℝ)|^33 ≤ (1715240928919/6250000000000 : ℝ)^25
        have hw : |(1877368973/5000000000 : ℝ)|=(1877368973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (647756139/2000000000 : ℝ)*x 0 + (346494521/500000000 : ℝ)*x 1 + (-247078157/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647756139/2000000000 : ℝ)^33 ≤ (22578944465497/100000000000000 : ℝ)^25 := by
    have hnat : (647756139 : ℕ)^33*100000000000000^25 ≤ 22578944465497^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647756139 2000000000 22578944465497 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346494521/500000000 : ℝ)^33 ≤ (240723694189/390625000000 : ℝ)^25 := by
    have hnat : (346494521 : ℕ)^33*390625000000^25 ≤ 240723694189^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346494521 500000000 240723694189 390625000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247078157/1000000000 : ℝ)^33 ≤ (15795789815421/100000000000000 : ℝ)^25 := by
    have hnat : (247078157 : ℕ)^33*100000000000000^25 ≤ 15795789815421^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247078157 1000000000 15795789815421 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647756139/2000000000 : ℝ), (346494521/500000000 : ℝ), (-247078157/1000000000 : ℝ)] ![(22578944465497/100000000000000 : ℝ), (240723694189/390625000000 : ℝ), (15795789815421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647756139/2000000000 : ℝ)|^33 ≤ (22578944465497/100000000000000 : ℝ)^25
        have hw : |(647756139/2000000000 : ℝ)|=(647756139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(346494521/500000000 : ℝ)|^33 ≤ (240723694189/390625000000 : ℝ)^25
        have hw : |(346494521/500000000 : ℝ)|=(346494521/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-247078157/1000000000 : ℝ)|^33 ≤ (15795789815421/100000000000000 : ℝ)^25
        have hw : |(-247078157/1000000000 : ℝ)|=(247078157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303083_s2_s2_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2132319963/5000000000 : ℝ)*x 0 + (4547554477/10000000000 : ℝ)*x 1 + (4237305731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132319963/5000000000 : ℝ)^33 ≤ (32467191785843/100000000000000 : ℝ)^25 := by
    have hnat : (2132319963 : ℕ)^33*100000000000000^25 ≤ 32467191785843^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132319963 5000000000 32467191785843 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4547554477/10000000000 : ℝ)^33 ≤ (35340024127193/100000000000000 : ℝ)^25 := by
    have hnat : (4547554477 : ℕ)^33*100000000000000^25 ≤ 35340024127193^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547554477 10000000000 35340024127193 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237305731/10000000000 : ℝ)^33 ≤ (16096392033977/50000000000000 : ℝ)^25 := by
    have hnat : (4237305731 : ℕ)^33*50000000000000^25 ≤ 16096392033977^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237305731 10000000000 16096392033977 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2132319963/5000000000 : ℝ), (4547554477/10000000000 : ℝ), (4237305731/10000000000 : ℝ)] ![(32467191785843/100000000000000 : ℝ), (35340024127193/100000000000000 : ℝ), (16096392033977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2132319963/5000000000 : ℝ)|^33 ≤ (32467191785843/100000000000000 : ℝ)^25
        have hw : |(2132319963/5000000000 : ℝ)|=(2132319963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4547554477/10000000000 : ℝ)|^33 ≤ (35340024127193/100000000000000 : ℝ)^25
        have hw : |(4547554477/10000000000 : ℝ)|=(4547554477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237305731/10000000000 : ℝ)|^33 ≤ (16096392033977/50000000000000 : ℝ)^25
        have hw : |(4237305731/10000000000 : ℝ)|=(4237305731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303083_s2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((64317/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64317/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((67581/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(67581/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36733/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36733/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4661/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4661/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((39379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(39379/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20629/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20629/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (64317/100000 : ℝ) ^ (131/32 : ℝ) ≤ (16418506822495821687/100000000000000000000 : ℝ) := by
    have hpowers : (64317/100000 : ℝ)^131 ≤ (16418506822495821687/100000000000000000000 : ℝ)^32 := by
      have hnat : (64317 : ℕ)^131*100000000000000000000^32 ≤ 16418506822495821687^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64317 100000 16418506822495821687 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64317/100000 : ℝ)) (X := (16418506822495821687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (116418506822495821687/100000000000000000000 : ℝ) ≤ (5189165497598007/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (116418506822495821687/100000000000000000000 : ℝ)^32 ≤ (5189165497598007/5000000000000000 : ℝ)^131 := by
      have hnat : (116418506822495821687 : ℕ)^32*5000000000000000^131 ≤ 5189165497598007^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116418506822495821687 100000000000000000000 5189165497598007 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5189165497598007/5000000000000000 : ℝ)) (X := (116418506822495821687/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (66418506822495821687/50000000000000000000 : ℝ) ≤ (2679561684709129/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (66418506822495821687/50000000000000000000 : ℝ)^32 ≤ (2679561684709129/2500000000000000 : ℝ)^131 := by
      have hnat : (66418506822495821687 : ℕ)^32*2500000000000000^131 ≤ 2679561684709129^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66418506822495821687 50000000000000000000 2679561684709129 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2679561684709129/2500000000000000 : ℝ)) (X := (66418506822495821687/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(189165497598007/3215850000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(169957871820251/3215850000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (64317/100000 : ℝ)) (alpha := (189165497598007/3215850000000000 : ℝ)) (beta := (169957871820251/3215850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (64317/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(189165497598007/3215850000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(169957871820251/3215850000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (67581/100000 : ℝ) ^ (131/32 : ℝ) ≤ (4021374394326758939/20000000000000000000 : ℝ) := by
    have hpowers : (67581/100000 : ℝ)^131 ≤ (4021374394326758939/20000000000000000000 : ℝ)^32 := by
      have hnat : (67581 : ℕ)^131*20000000000000000000^32 ≤ 4021374394326758939^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67581 100000 4021374394326758939 20000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67581/100000 : ℝ)) (X := (4021374394326758939/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (24021374394326758939/20000000000000000000 : ℝ) ≤ (1045770587277179/1000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (24021374394326758939/20000000000000000000 : ℝ)^32 ≤ (1045770587277179/1000000000000000 : ℝ)^131 := by
      have hnat : (24021374394326758939 : ℕ)^32*1000000000000000^131 ≤ 1045770587277179^131*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24021374394326758939 20000000000000000000 1045770587277179 1000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1045770587277179/1000000000000000 : ℝ)) (X := (24021374394326758939/20000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (14021374394326758939/10000000000000000000 : ℝ) ≤ (10860685615525243/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (14021374394326758939/10000000000000000000 : ℝ)^32 ≤ (10860685615525243/10000000000000000 : ℝ)^131 := by
      have hnat : (14021374394326758939 : ℕ)^32*10000000000000000^131 ≤ 10860685615525243^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14021374394326758939 10000000000000000000 10860685615525243 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10860685615525243/10000000000000000 : ℝ)) (X := (14021374394326758939/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(45770587277179/675810000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(402979742753453/6758100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (67581/100000 : ℝ)) (alpha := (45770587277179/675810000000000 : ℝ)) (beta := (402979742753453/6758100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (67581/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(45770587277179/675810000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(402979742753453/6758100000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (36733/50000 : ℝ) ^ (131/32 : ℝ) ≤ (5660061799272877091/20000000000000000000 : ℝ) := by
    have hpowers : (36733/50000 : ℝ)^131 ≤ (5660061799272877091/20000000000000000000 : ℝ)^32 := by
      have hnat : (36733 : ℕ)^131*20000000000000000000^32 ≤ 5660061799272877091^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36733 50000 5660061799272877091 20000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36733/50000 : ℝ)) (X := (5660061799272877091/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (25660061799272877091/20000000000000000000 : ℝ) ≤ (2125530283674587/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (25660061799272877091/20000000000000000000 : ℝ)^32 ≤ (2125530283674587/2000000000000000 : ℝ)^131 := by
      have hnat : (25660061799272877091 : ℕ)^32*2000000000000000^131 ≤ 2125530283674587^131*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25660061799272877091 20000000000000000000 2125530283674587 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2125530283674587/2000000000000000 : ℝ)) (X := (25660061799272877091/20000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (15660061799272877091/10000000000000000000 : ℝ) ≤ (2789479324382441/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (15660061799272877091/10000000000000000000 : ℝ)^32 ≤ (2789479324382441/2500000000000000 : ℝ)^131 := by
      have hnat : (15660061799272877091 : ℕ)^32*2500000000000000^131 ≤ 2789479324382441^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15660061799272877091 10000000000000000000 2789479324382441 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2789479324382441/2500000000000000 : ℝ)) (X := (15660061799272877091/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(125530283674587/1469320000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(530265879156829/7346600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (36733/50000 : ℝ)) (alpha := (125530283674587/1469320000000000 : ℝ)) (beta := (530265879156829/7346600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (36733/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(125530283674587/1469320000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(530265879156829/7346600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1193494731/5000000000 : ℝ)*X 0 0+(1005320361/2000000000 : ℝ)*X 0 1+(1355442553/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((1741834809/2500000000 : ℝ)*X 1 0+(-95868923/1000000000 : ℝ)*X 1 1+(4357906841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((3790781411/10000000000 : ℝ)*X 2 0+(6447785219/10000000000 : ℝ)*X 2 1+(-1257952919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2355829517/10000000000 : ℝ)*X 0 0+(4997615423/10000000000 : ℝ)*X 0 1+(5473872127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((6479520607/10000000000 : ℝ)*X 1 0+(-2698361/10000000000 : ℝ)*X 1 1+(2666126067/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((778326823/2500000000 : ℝ)*X 2 0+(7574162597/10000000000 : ℝ)*X 2 1+(-165004547/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((3063110179/10000000000 : ℝ)*X 0 0+(965880939/2000000000 : ℝ)*X 0 1+(5067039903/10000000000 : ℝ)*X 0 2+(3063110179/10000000000 : ℝ)*X 1 0+(965880939/2000000000 : ℝ)*X 1 1+(5067039903/10000000000 : ℝ)*X 1 2+(3063110179/10000000000 : ℝ)*X 2 0+(965880939/2000000000 : ℝ)*X 2 1+(5067039903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1279490961/10000000000 : ℝ)*X 0 0+(3661137817/10000000000 : ℝ)*X 0 1+(7368816263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1660597233/2000000000 : ℝ)*X 1 0+(-28530671/500000000 : ℝ)*X 1 1+(2896619157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((4057300427/10000000000 : ℝ)*X 2 0+(861071841/1250000000 : ℝ)*X 2 1+(-192434969/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1344935129/5000000000 : ℝ)*X 0 0+(465305929/1250000000 : ℝ)*X 0 1+(6375009101/10000000000 : ℝ)*X 0 2+(1344935129/5000000000 : ℝ)*X 1 0+(465305929/1250000000 : ℝ)*X 1 1+(6375009101/10000000000 : ℝ)*X 1 2+(1344935129/5000000000 : ℝ)*X 2 0+(465305929/1250000000 : ℝ)*X 2 1+(6375009101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-888294413/5000000000 : ℝ)*X 0 0+(115317211/200000000 : ℝ)*X 0 1+(2565108271/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((980039481/1250000000 : ℝ)*X 1 0+(-19069941/10000000000 : ℝ)*X 1 1+(1877368973/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((647756139/2000000000 : ℝ)*X 2 0+(346494521/500000000 : ℝ)*X 2 1+(-247078157/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2132319963/5000000000 : ℝ)*X 0 0+(4547554477/10000000000 : ℝ)*X 0 1+(4237305731/10000000000 : ℝ)*X 0 2+(2132319963/5000000000 : ℝ)*X 1 0+(4547554477/10000000000 : ℝ)*X 1 1+(4237305731/10000000000 : ℝ)*X 1 2+(2132319963/5000000000 : ℝ)*X 2 0+(4547554477/10000000000 : ℝ)*X 2 1+(4237305731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303083_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((4661/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4661/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (898390570072643307351517898547/197115952386100000000000000000000000 : ℝ) := by norm_num
    linear_combination (1464761/200000000000 : ℝ)*(base19) + (4242709/500000000000 : ℝ)*(base23) + (598186421/40000000000 : ℝ)*(base40) + (81836124759/100000000000 : ℝ)*(base49) + (155538268969/500000000000 : ℝ)*(base60) + (3710484441063/1000000000000 : ℝ)*(major_s2_0) + (3710484441063/1000000000000 : ℝ)*(major_s2_1) + (3710484441063/1000000000000 : ℝ)*(major_s2_2) + (2212829/8000000000 : ℝ)*(sp_s2_0) + (4953899304727/1000000000000 : ℝ)*(sp_s2_7) + (2477105321679/500000000000 : ℝ)*(sp_s2_8) + (309638092609/62500000000 : ℝ)*(sp_s2_9) + (1233374697867/500000000000 : ℝ)*(sp_s2_13) + (4205881/100000000000 : ℝ)*(sp_s2_21) + (1233374697867/500000000000 : ℝ)*(f.failure) + (2477108983581/500000000000 : ℝ)*(f.sum) + (2797902434753438993/18388539800000000000000000000000 : ℝ)*base63 + (2510555083463067/7346600000000000000000000000 : ℝ)*base65 + (6115046380649/12515000000000000000000000 : ℝ)*base67 + (669702653961037/1469320000000000000000000000 : ℝ)*base69 + (11093781563035879423/157503757400000000000000000000000 : ℝ)*base70 + (527306320651659/1071950000000000000000000000 : ℝ)*base72 + (111964757383923/250300000000000000000000000 : ℝ)*base75 + (966793639143037/1071950000000000000000000000 : ℝ)*base77 + (242414621014591403/670772712500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (207/2500000000000000 : ℝ)*base87 + (207/2500000000000000 : ℝ)*base89 + (207/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((39379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(39379/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2330327624183805719115581/715926170000000000000000000000 : ℝ) := by norm_num
    linear_combination (1143117/250000000000 : ℝ)*(base21) + (712658848429/1000000000000 : ℝ)*(base40) + (646584462147/1000000000000 : ℝ)*(base49) + (297086661409/500000000000 : ℝ)*(base60) + (735365150377/250000000000 : ℝ)*(major_s2_0) + (735365150377/250000000000 : ℝ)*(major_s2_1) + (735365150377/250000000000 : ℝ)*(major_s2_2) + (3635731/1000000000000 : ℝ)*(sp_s2_1) + (513167/250000000000 : ℝ)*(sp_s2_2) + (3927421779021/1000000000000 : ℝ)*(sp_s2_14) + (3927405210123/1000000000000 : ℝ)*(sp_s2_15) + (981853788471/250000000000 : ℝ)*(sp_s2_16) + (1955498338989/1000000000000 : ℝ)*(sp_s2_20) + (808323/62500000000 : ℝ)*(sp_s2_22) + (1955498338989/1000000000000 : ℝ)*(f.failure) + (3927421779021/1000000000000 : ℝ)*(f.sum) + (282525269475155177/15515330456250000000000000000000 : ℝ)*base62 + (197884344274401/229581250000000000000000000 : ℝ)*base65 + (8568923208139/16895250000000000000000000 : ℝ)*base67 + (161256305854011/183665000000000000000000000 : ℝ)*base68 + (10269000854198801969/10738892550000000000000000000000 : ℝ)*base71 + (42502801861037/292350000000000000000000000 : ℝ)*base72 + (1080003761572337/844762500000000000000000000 : ℝ)*base75 + (4989878773109/4567968750000000000000000 : ℝ)*base77 + (961122804958971269/6585768450000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base84 + (3731/5000000000000000 : ℝ)*base86 + (3731/5000000000000000 : ℝ)*base88 + (3731/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20629/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20629/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1177514611100478208544143771/78751878700000000000000000000000 : ℝ) := by norm_num
    linear_combination (1501369/250000000000 : ℝ)*(base11) + (172279066529/250000000000 : ℝ)*(base40) + (916295726841/1000000000000 : ℝ)*(base49) + (4585751/1000000000000 : ℝ)*(base50) + (4083035241163/1000000000000 : ℝ)*(major_s2_0) + (4083035241163/1000000000000 : ℝ)*(major_s2_1) + (4083035241163/1000000000000 : ℝ)*(major_s2_2) + (6966773/1000000000000 : ℝ)*(sp_s2_9) + (15364173/250000000000 : ℝ)*(sp_s2_15) + (15720067/250000000000 : ℝ)*(sp_s2_16) + (1362909095843/250000000000 : ℝ)*(sp_s2_21) + (1362895233039/250000000000 : ℝ)*(sp_s2_22) + (5451572541807/1000000000000 : ℝ)*(sp_s2_23) + (2714423109403/1000000000000 : ℝ)*(sp_s2_27) + (2714423109403/1000000000000 : ℝ)*(f.failure) + (340727649303/62500000000 : ℝ)*(f.sum) + (76094947467427006571/496490574600000000000000000000000 : ℝ)*base63 + (6019156097010333/7346600000000000000000000000 : ℝ)*base64 + (1733911756139/6758100000000000000000000 : ℝ)*base66 + (1110343238829391/1469320000000000000000000000 : ℝ)*base68 + (137610059904670426229/472511272200000000000000000000000 : ℝ)*base70 + (492387817034173/803962500000000000000000000 : ℝ)*base72 + (1663095048398789/6758100000000000000000000000 : ℝ)*base74 + (2546693197776119/3215850000000000000000000000 : ℝ)*base76 + (11107578550496759351/72443452950000000000000000000000 : ℝ)*base79 + (4963/5000000000000000 : ℝ)*base87 + (4963/5000000000000000 : ℝ)*base89 + (4963/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((64317/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64317/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((67581/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(67581/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36733/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36733/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4661/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4661/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((39379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(39379/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20629/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20629/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303083_s2 p hpa hpb X hX hprev1

#print axioms solution
