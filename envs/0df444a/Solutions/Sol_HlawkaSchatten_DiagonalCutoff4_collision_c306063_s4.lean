-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306063_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:59:03.28447+00:00
-- url     : https://prove2.me/submissions/b10f3272-5b6b-4bdc-a35f-78c3b2d03d9d

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
theorem collision_support_c306063_s4_s4_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-277608151/2500000000 : ℝ)*x 0 + (5576235339/10000000000 : ℝ)*x 1 + (5701377151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277608151/2500000000 : ℝ)^135 ≤ (1121956681933/20000000000000 : ℝ)^103 := by
    have hnat : (277608151 : ℕ)^135*20000000000000^103 ≤ 1121956681933^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277608151 2500000000 1121956681933 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5576235339/10000000000 : ℝ)^135 ≤ (23254363051067/50000000000000 : ℝ)^103 := by
    have hnat : (5576235339 : ℕ)^135*50000000000000^103 ≤ 23254363051067^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5576235339 10000000000 23254363051067 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5701377151/10000000000 : ℝ)^135 ≤ (47881490480953/100000000000000 : ℝ)^103 := by
    have hnat : (5701377151 : ℕ)^135*100000000000000^103 ≤ 47881490480953^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5701377151 10000000000 47881490480953 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-277608151/2500000000 : ℝ), (5576235339/10000000000 : ℝ), (5701377151/10000000000 : ℝ)] ![(1121956681933/20000000000000 : ℝ), (23254363051067/50000000000000 : ℝ), (47881490480953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-277608151/2500000000 : ℝ)|^135 ≤ (1121956681933/20000000000000 : ℝ)^103
        have hw : |(-277608151/2500000000 : ℝ)|=(277608151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5576235339/10000000000 : ℝ)|^135 ≤ (23254363051067/50000000000000 : ℝ)^103
        have hw : |(5576235339/10000000000 : ℝ)|=(5576235339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5701377151/10000000000 : ℝ)|^135 ≤ (47881490480953/100000000000000 : ℝ)^103
        have hw : |(5701377151/10000000000 : ℝ)|=(5701377151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5576980049/10000000000 : ℝ)*x 0 + (-1121121893/10000000000 : ℝ)*x 1 + (2847098243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5576980049/10000000000 : ℝ)^135 ≤ (9303373451671/20000000000000 : ℝ)^103 := by
    have hnat : (5576980049 : ℕ)^135*20000000000000^103 ≤ 9303373451671^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5576980049 10000000000 9303373451671 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121121893/10000000000 : ℝ)^135 ≤ (5680667171087/100000000000000 : ℝ)^103 := by
    have hnat : (1121121893 : ℕ)^135*100000000000000^103 ≤ 5680667171087^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121121893 10000000000 5680667171087 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2847098243/5000000000 : ℝ)^135 ≤ (47802465554637/100000000000000 : ℝ)^103 := by
    have hnat : (2847098243 : ℕ)^135*100000000000000^103 ≤ 47802465554637^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847098243 5000000000 47802465554637 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5576980049/10000000000 : ℝ), (-1121121893/10000000000 : ℝ), (2847098243/5000000000 : ℝ)] ![(9303373451671/20000000000000 : ℝ), (5680667171087/100000000000000 : ℝ), (47802465554637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5576980049/10000000000 : ℝ)|^135 ≤ (9303373451671/20000000000000 : ℝ)^103
        have hw : |(5576980049/10000000000 : ℝ)|=(5576980049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1121121893/10000000000 : ℝ)|^135 ≤ (5680667171087/100000000000000 : ℝ)^103
        have hw : |(-1121121893/10000000000 : ℝ)|=(1121121893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2847098243/5000000000 : ℝ)|^135 ≤ (47802465554637/100000000000000 : ℝ)^103
        have hw : |(2847098243/5000000000 : ℝ)|=(2847098243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (112645871/200000000 : ℝ)*x 0 + (1134995133/2000000000 : ℝ)*x 1 + (-132656769/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112645871/200000000 : ℝ)^135 ≤ (47122495530259/100000000000000 : ℝ)^103 := by
    have hnat : (112645871 : ℕ)^135*100000000000000^103 ≤ 47122495530259^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112645871 200000000 47122495530259 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134995133/2000000000 : ℝ)^135 ≤ (23795544122321/50000000000000 : ℝ)^103 := by
    have hnat : (1134995133 : ℕ)^135*50000000000000^103 ≤ 23795544122321^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134995133 2000000000 23795544122321 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132656769/1250000000 : ℝ)^135 ≤ (2643208102649/50000000000000 : ℝ)^103 := by
    have hnat : (132656769 : ℕ)^135*50000000000000^103 ≤ 2643208102649^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132656769 1250000000 2643208102649 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112645871/200000000 : ℝ), (1134995133/2000000000 : ℝ), (-132656769/1250000000 : ℝ)] ![(47122495530259/100000000000000 : ℝ), (23795544122321/50000000000000 : ℝ), (2643208102649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112645871/200000000 : ℝ)|^135 ≤ (47122495530259/100000000000000 : ℝ)^103
        have hw : |(112645871/200000000 : ℝ)|=(112645871/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134995133/2000000000 : ℝ)|^135 ≤ (23795544122321/50000000000000 : ℝ)^103
        have hw : |(1134995133/2000000000 : ℝ)|=(1134995133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-132656769/1250000000 : ℝ)|^135 ≤ (2643208102649/50000000000000 : ℝ)^103
        have hw : |(-132656769/1250000000 : ℝ)|=(132656769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (557472197/1250000000 : ℝ)*x 0 + (1086774473/2500000000 : ℝ)*x 1 + (4166188321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (557472197/1250000000 : ℝ)^135 ≤ (34702595700151/100000000000000 : ℝ)^103 := by
    have hnat : (557472197 : ℕ)^135*100000000000000^103 ≤ 34702595700151^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557472197 1250000000 34702595700151 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086774473/2500000000 : ℝ)^135 ≤ (8389486222621/25000000000000 : ℝ)^103 := by
    have hnat : (1086774473 : ℕ)^135*25000000000000^103 ≤ 8389486222621^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086774473 2500000000 8389486222621 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4166188321/10000000000 : ℝ)^135 ≤ (31739459398317/100000000000000 : ℝ)^103 := by
    have hnat : (4166188321 : ℕ)^135*100000000000000^103 ≤ 31739459398317^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166188321 10000000000 31739459398317 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(557472197/1250000000 : ℝ), (1086774473/2500000000 : ℝ), (4166188321/10000000000 : ℝ)] ![(34702595700151/100000000000000 : ℝ), (8389486222621/25000000000000 : ℝ), (31739459398317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(557472197/1250000000 : ℝ)|^135 ≤ (34702595700151/100000000000000 : ℝ)^103
        have hw : |(557472197/1250000000 : ℝ)|=(557472197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086774473/2500000000 : ℝ)|^135 ≤ (8389486222621/25000000000000 : ℝ)^103
        have hw : |(1086774473/2500000000 : ℝ)|=(1086774473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4166188321/10000000000 : ℝ)|^135 ≤ (31739459398317/100000000000000 : ℝ)^103
        have hw : |(4166188321/10000000000 : ℝ)|=(4166188321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-198254989/2500000000 : ℝ)*x 0 + (2237040493/5000000000 : ℝ)*x 1 + (1380961101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198254989/2500000000 : ℝ)^135 ≤ (1804197751879/50000000000000 : ℝ)^103 := by
    have hnat : (198254989 : ℕ)^135*50000000000000^103 ≤ 1804197751879^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198254989 2500000000 1804197751879 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237040493/5000000000 : ℝ)^135 ≤ (17424272337299/50000000000000 : ℝ)^103 := by
    have hnat : (2237040493 : ℕ)^135*50000000000000^103 ≤ 17424272337299^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237040493 5000000000 17424272337299 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380961101/2000000000 : ℝ)^135 ≤ (12308611961177/20000000000000 : ℝ)^103 := by
    have hnat : (1380961101 : ℕ)^135*20000000000000^103 ≤ 12308611961177^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380961101 2000000000 12308611961177 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-198254989/2500000000 : ℝ), (2237040493/5000000000 : ℝ), (1380961101/2000000000 : ℝ)] ![(1804197751879/50000000000000 : ℝ), (17424272337299/50000000000000 : ℝ), (12308611961177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-198254989/2500000000 : ℝ)|^135 ≤ (1804197751879/50000000000000 : ℝ)^103
        have hw : |(-198254989/2500000000 : ℝ)|=(198254989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237040493/5000000000 : ℝ)|^135 ≤ (17424272337299/50000000000000 : ℝ)^103
        have hw : |(2237040493/5000000000 : ℝ)|=(2237040493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1380961101/2000000000 : ℝ)|^135 ≤ (12308611961177/20000000000000 : ℝ)^103
        have hw : |(1380961101/2000000000 : ℝ)|=(1380961101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (191486227/400000000 : ℝ)*x 0 + (-82975309/5000000000 : ℝ)*x 1 + (689740709/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191486227/400000000 : ℝ)^135 ≤ (9519720048103/25000000000000 : ℝ)^103 := by
    have hnat : (191486227 : ℕ)^135*25000000000000^103 ≤ 9519720048103^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191486227 400000000 9519720048103 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82975309/5000000000 : ℝ)^135 ≤ (58059409561/12500000000000 : ℝ)^103 := by
    have hnat : (82975309 : ℕ)^135*12500000000000^103 ≤ 58059409561^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82975309 5000000000 58059409561 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689740709/1000000000 : ℝ)^135 ≤ (15364161130677/25000000000000 : ℝ)^103 := by
    have hnat : (689740709 : ℕ)^135*25000000000000^103 ≤ 15364161130677^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689740709 1000000000 15364161130677 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(191486227/400000000 : ℝ), (-82975309/5000000000 : ℝ), (689740709/1000000000 : ℝ)] ![(9519720048103/25000000000000 : ℝ), (58059409561/12500000000000 : ℝ), (15364161130677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(191486227/400000000 : ℝ)|^135 ≤ (9519720048103/25000000000000 : ℝ)^103
        have hw : |(191486227/400000000 : ℝ)|=(191486227/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-82975309/5000000000 : ℝ)|^135 ≤ (58059409561/12500000000000 : ℝ)^103
        have hw : |(-82975309/5000000000 : ℝ)|=(82975309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(689740709/1000000000 : ℝ)|^135 ≤ (15364161130677/25000000000000 : ℝ)^103
        have hw : |(689740709/1000000000 : ℝ)|=(689740709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4516904939/10000000000 : ℝ)*x 0 + (7163548821/10000000000 : ℝ)*x 1 + (-15742637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4516904939/10000000000 : ℝ)^135 ≤ (1102699284921/3125000000000 : ℝ)^103 := by
    have hnat : (4516904939 : ℕ)^135*3125000000000^103 ≤ 1102699284921^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516904939 10000000000 1102699284921 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7163548821/10000000000 : ℝ)^135 ≤ (64583193814403/100000000000000 : ℝ)^103 := by
    have hnat : (7163548821 : ℕ)^135*100000000000000^103 ≤ 64583193814403^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7163548821 10000000000 64583193814403 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15742637/2500000000 : ℝ)^135 ≤ (130429057947/100000000000000 : ℝ)^103 := by
    have hnat : (15742637 : ℕ)^135*100000000000000^103 ≤ 130429057947^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15742637 2500000000 130429057947 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4516904939/10000000000 : ℝ), (7163548821/10000000000 : ℝ), (-15742637/2500000000 : ℝ)] ![(1102699284921/3125000000000 : ℝ), (64583193814403/100000000000000 : ℝ), (130429057947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4516904939/10000000000 : ℝ)|^135 ≤ (1102699284921/3125000000000 : ℝ)^103
        have hw : |(4516904939/10000000000 : ℝ)|=(4516904939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7163548821/10000000000 : ℝ)|^135 ≤ (64583193814403/100000000000000 : ℝ)^103
        have hw : |(7163548821/10000000000 : ℝ)|=(7163548821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15742637/2500000000 : ℝ)|^135 ≤ (130429057947/100000000000000 : ℝ)^103
        have hw : |(-15742637/2500000000 : ℝ)|=(15742637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (218507763/500000000 : ℝ)*x 0 + (3125807947/5000000000 : ℝ)*x 1 + (1003215219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218507763/500000000 : ℝ)^135 ≤ (16895715072821/50000000000000 : ℝ)^103 := by
    have hnat : (218507763 : ℕ)^135*50000000000000^103 ≤ 16895715072821^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218507763 500000000 16895715072821 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3125807947/5000000000 : ℝ)^135 ≤ (54027049349419/100000000000000 : ℝ)^103 := by
    have hnat : (3125807947 : ℕ)^135*100000000000000^103 ≤ 54027049349419^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3125807947 5000000000 54027049349419 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003215219/5000000000 : ℝ)^135 ≤ (6090760246777/50000000000000 : ℝ)^103 := by
    have hnat : (1003215219 : ℕ)^135*50000000000000^103 ≤ 6090760246777^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003215219 5000000000 6090760246777 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218507763/500000000 : ℝ), (3125807947/5000000000 : ℝ), (1003215219/5000000000 : ℝ)] ![(16895715072821/50000000000000 : ℝ), (54027049349419/100000000000000 : ℝ), (6090760246777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218507763/500000000 : ℝ)|^135 ≤ (16895715072821/50000000000000 : ℝ)^103
        have hw : |(218507763/500000000 : ℝ)|=(218507763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3125807947/5000000000 : ℝ)|^135 ≤ (54027049349419/100000000000000 : ℝ)^103
        have hw : |(3125807947/5000000000 : ℝ)|=(3125807947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003215219/5000000000 : ℝ)|^135 ≤ (6090760246777/50000000000000 : ℝ)^103
        have hw : |(1003215219/5000000000 : ℝ)|=(1003215219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-18111139/1250000000 : ℝ)*x 0 + (4743605619/10000000000 : ℝ)*x 1 + (6942666189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18111139/1250000000 : ℝ)^135 ≤ (194391403893/50000000000000 : ℝ)^103 := by
    have hnat : (18111139 : ℕ)^135*50000000000000^103 ≤ 194391403893^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18111139 1250000000 194391403893 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4743605619/10000000000 : ℝ)^135 ≤ (37625485507869/100000000000000 : ℝ)^103 := by
    have hnat : (4743605619 : ℕ)^135*100000000000000^103 ≤ 37625485507869^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4743605619 10000000000 37625485507869 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6942666189/10000000000 : ℝ)^135 ≤ (15496432919999/25000000000000 : ℝ)^103 := by
    have hnat : (6942666189 : ℕ)^135*25000000000000^103 ≤ 15496432919999^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6942666189 10000000000 15496432919999 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18111139/1250000000 : ℝ), (4743605619/10000000000 : ℝ), (6942666189/10000000000 : ℝ)] ![(194391403893/50000000000000 : ℝ), (37625485507869/100000000000000 : ℝ), (15496432919999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18111139/1250000000 : ℝ)|^135 ≤ (194391403893/50000000000000 : ℝ)^103
        have hw : |(-18111139/1250000000 : ℝ)|=(18111139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4743605619/10000000000 : ℝ)|^135 ≤ (37625485507869/100000000000000 : ℝ)^103
        have hw : |(4743605619/10000000000 : ℝ)|=(4743605619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6942666189/10000000000 : ℝ)|^135 ≤ (15496432919999/25000000000000 : ℝ)^103
        have hw : |(6942666189/10000000000 : ℝ)|=(6942666189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (553264083/1250000000 : ℝ)*x 0 + (-6522563/80000000 : ℝ)*x 1 + (1387039899/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553264083/1250000000 : ℝ)^135 ≤ (34359660273341/100000000000000 : ℝ)^103 := by
    have hnat : (553264083 : ℕ)^135*100000000000000^103 ≤ 34359660273341^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553264083 1250000000 34359660273341 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6522563/80000000 : ℝ)^135 ≤ (233873066753/6250000000000 : ℝ)^103 := by
    have hnat : (6522563 : ℕ)^135*6250000000000^103 ≤ 233873066753^103*80000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6522563 80000000 233873066753 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1387039899/2000000000 : ℝ)^135 ≤ (61898370646029/100000000000000 : ℝ)^103 := by
    have hnat : (1387039899 : ℕ)^135*100000000000000^103 ≤ 61898370646029^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387039899 2000000000 61898370646029 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(553264083/1250000000 : ℝ), (-6522563/80000000 : ℝ), (1387039899/2000000000 : ℝ)] ![(34359660273341/100000000000000 : ℝ), (233873066753/6250000000000 : ℝ), (61898370646029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(553264083/1250000000 : ℝ)|^135 ≤ (34359660273341/100000000000000 : ℝ)^103
        have hw : |(553264083/1250000000 : ℝ)|=(553264083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6522563/80000000 : ℝ)|^135 ≤ (233873066753/6250000000000 : ℝ)^103
        have hw : |(-6522563/80000000 : ℝ)|=(6522563/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1387039899/2000000000 : ℝ)|^135 ≤ (61898370646029/100000000000000 : ℝ)^103
        have hw : |(1387039899/2000000000 : ℝ)|=(1387039899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1373313959/2000000000 : ℝ)*x 0 + (2423140663/5000000000 : ℝ)*x 1 + (-44745901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1373313959/2000000000 : ℝ)^135 ≤ (61096767788293/100000000000000 : ℝ)^103 := by
    have hnat : (1373313959 : ℕ)^135*100000000000000^103 ≤ 61096767788293^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373313959 2000000000 61096767788293 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2423140663/5000000000 : ℝ)^135 ≤ (38696482886669/100000000000000 : ℝ)^103 := by
    have hnat : (2423140663 : ℕ)^135*100000000000000^103 ≤ 38696482886669^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423140663 5000000000 38696482886669 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44745901/5000000000 : ℝ)^135 ≤ (103374655181/50000000000000 : ℝ)^103 := by
    have hnat : (44745901 : ℕ)^135*50000000000000^103 ≤ 103374655181^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44745901 5000000000 103374655181 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1373313959/2000000000 : ℝ), (2423140663/5000000000 : ℝ), (-44745901/5000000000 : ℝ)] ![(61096767788293/100000000000000 : ℝ), (38696482886669/100000000000000 : ℝ), (103374655181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1373313959/2000000000 : ℝ)|^135 ≤ (61096767788293/100000000000000 : ℝ)^103
        have hw : |(1373313959/2000000000 : ℝ)|=(1373313959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2423140663/5000000000 : ℝ)|^135 ≤ (38696482886669/100000000000000 : ℝ)^103
        have hw : |(2423140663/5000000000 : ℝ)|=(2423140663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44745901/5000000000 : ℝ)|^135 ≤ (103374655181/50000000000000 : ℝ)^103
        have hw : |(-44745901/5000000000 : ℝ)|=(44745901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (700782057/1000000000 : ℝ)*x 0 + (697301147/2000000000 : ℝ)*x 1 + (1998581863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (700782057/1000000000 : ℝ)^135 ≤ (62749280680927/100000000000000 : ℝ)^103 := by
    have hnat : (700782057 : ℕ)^135*100000000000000^103 ≤ 62749280680927^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700782057 1000000000 62749280680927 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (697301147/2000000000 : ℝ)^135 ≤ (2513161546993/10000000000000 : ℝ)^103 := by
    have hnat : (697301147 : ℕ)^135*10000000000000^103 ≤ 2513161546993^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697301147 2000000000 2513161546993 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1998581863/10000000000 : ℝ)^135 ≤ (12119103832213/100000000000000 : ℝ)^103 := by
    have hnat : (1998581863 : ℕ)^135*100000000000000^103 ≤ 12119103832213^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998581863 10000000000 12119103832213 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(700782057/1000000000 : ℝ), (697301147/2000000000 : ℝ), (1998581863/10000000000 : ℝ)] ![(62749280680927/100000000000000 : ℝ), (2513161546993/10000000000000 : ℝ), (12119103832213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(700782057/1000000000 : ℝ)|^135 ≤ (62749280680927/100000000000000 : ℝ)^103
        have hw : |(700782057/1000000000 : ℝ)|=(700782057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(697301147/2000000000 : ℝ)|^135 ≤ (2513161546993/10000000000000 : ℝ)^103
        have hw : |(697301147/2000000000 : ℝ)|=(697301147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1998581863/10000000000 : ℝ)|^135 ≤ (12119103832213/100000000000000 : ℝ)^103
        have hw : |(1998581863/10000000000 : ℝ)|=(1998581863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-623213/62500000 : ℝ)*x 0 + (6480937679/10000000000 : ℝ)*x 1 + (1315929611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (623213/62500000 : ℝ)^135 ≤ (238237942159/100000000000000 : ℝ)^103 := by
    have hnat : (623213 : ℕ)^135*100000000000000^103 ≤ 238237942159^103*62500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623213 62500000 238237942159 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6480937679/10000000000 : ℝ)^135 ≤ (56639259165167/100000000000000 : ℝ)^103 := by
    have hnat : (6480937679 : ℕ)^135*100000000000000^103 ≤ 56639259165167^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6480937679 10000000000 56639259165167 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315929611/2500000000 : ℝ)^135 ≤ (1724900115097/4000000000000 : ℝ)^103 := by
    have hnat : (1315929611 : ℕ)^135*4000000000000^103 ≤ 1724900115097^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315929611 2500000000 1724900115097 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-623213/62500000 : ℝ), (6480937679/10000000000 : ℝ), (1315929611/2500000000 : ℝ)] ![(238237942159/100000000000000 : ℝ), (56639259165167/100000000000000 : ℝ), (1724900115097/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-623213/62500000 : ℝ)|^135 ≤ (238237942159/100000000000000 : ℝ)^103
        have hw : |(-623213/62500000 : ℝ)|=(623213/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6480937679/10000000000 : ℝ)|^135 ≤ (56639259165167/100000000000000 : ℝ)^103
        have hw : |(6480937679/10000000000 : ℝ)|=(6480937679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315929611/2500000000 : ℝ)|^135 ≤ (1724900115097/4000000000000 : ℝ)^103
        have hw : |(1315929611/2500000000 : ℝ)|=(1315929611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6852785667/10000000000 : ℝ)*x 0 + (-17554331/2000000000 : ℝ)*x 1 + (607765603/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6852785667/10000000000 : ℝ)^135 ≤ (30468033366891/50000000000000 : ℝ)^103 := by
    have hnat : (6852785667 : ℕ)^135*50000000000000^103 ≤ 30468033366891^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6852785667 10000000000 30468033366891 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17554331/2000000000 : ℝ)^135 ≤ (40311261739/20000000000000 : ℝ)^103 := by
    have hnat : (17554331 : ℕ)^135*20000000000000^103 ≤ 40311261739^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17554331 2000000000 40311261739 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (607765603/1250000000 : ℝ)^135 ≤ (9715594235113/25000000000000 : ℝ)^103 := by
    have hnat : (607765603 : ℕ)^135*25000000000000^103 ≤ 9715594235113^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607765603 1250000000 9715594235113 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6852785667/10000000000 : ℝ), (-17554331/2000000000 : ℝ), (607765603/1250000000 : ℝ)] ![(30468033366891/50000000000000 : ℝ), (40311261739/20000000000000 : ℝ), (9715594235113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6852785667/10000000000 : ℝ)|^135 ≤ (30468033366891/50000000000000 : ℝ)^103
        have hw : |(6852785667/10000000000 : ℝ)|=(6852785667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17554331/2000000000 : ℝ)|^135 ≤ (40311261739/20000000000000 : ℝ)^103
        have hw : |(-17554331/2000000000 : ℝ)|=(17554331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(607765603/1250000000 : ℝ)|^135 ≤ (9715594235113/25000000000000 : ℝ)^103
        have hw : |(607765603/1250000000 : ℝ)|=(607765603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4414744549/10000000000 : ℝ)*x 0 + (6977717921/10000000000 : ℝ)*x 1 + (-150194803/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4414744549/10000000000 : ℝ)^135 ≤ (8561009734029/25000000000000 : ℝ)^103 := by
    have hnat : (4414744549 : ℕ)^135*25000000000000^103 ≤ 8561009734029^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4414744549 10000000000 8561009734029 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6977717921/10000000000 : ℝ)^135 ≤ (6239623015759/10000000000000 : ℝ)^103 := by
    have hnat : (6977717921 : ℕ)^135*10000000000000^103 ≤ 6239623015759^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6977717921 10000000000 6239623015759 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150194803/2000000000 : ℝ)^135 ≤ (3359730899439/100000000000000 : ℝ)^103 := by
    have hnat : (150194803 : ℕ)^135*100000000000000^103 ≤ 3359730899439^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150194803 2000000000 3359730899439 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4414744549/10000000000 : ℝ), (6977717921/10000000000 : ℝ), (-150194803/2000000000 : ℝ)] ![(8561009734029/25000000000000 : ℝ), (6239623015759/10000000000000 : ℝ), (3359730899439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4414744549/10000000000 : ℝ)|^135 ≤ (8561009734029/25000000000000 : ℝ)^103
        have hw : |(4414744549/10000000000 : ℝ)|=(4414744549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6977717921/10000000000 : ℝ)|^135 ≤ (6239623015759/10000000000000 : ℝ)^103
        have hw : |(6977717921/10000000000 : ℝ)|=(6977717921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-150194803/2000000000 : ℝ)|^135 ≤ (3359730899439/100000000000000 : ℝ)^103
        have hw : |(-150194803/2000000000 : ℝ)|=(150194803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s4_s4_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1786787271/2500000000 : ℝ)*x 0 + (353546227/1250000000 : ℝ)*x 1 + (316225343/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1786787271/2500000000 : ℝ)^135 ≤ (4024342233123/6250000000000 : ℝ)^103 := by
    have hnat : (1786787271 : ℕ)^135*6250000000000^103 ≤ 4024342233123^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786787271 2500000000 4024342233123 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353546227/1250000000 : ℝ)^135 ≤ (76418703079/400000000000 : ℝ)^103 := by
    have hnat : (353546227 : ℕ)^135*400000000000^103 ≤ 76418703079^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353546227 1250000000 76418703079 400000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316225343/1250000000 : ℝ)^135 ≤ (8252924246919/50000000000000 : ℝ)^103 := by
    have hnat : (316225343 : ℕ)^135*50000000000000^103 ≤ 8252924246919^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316225343 1250000000 8252924246919 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1786787271/2500000000 : ℝ), (353546227/1250000000 : ℝ), (316225343/1250000000 : ℝ)] ![(4024342233123/6250000000000 : ℝ), (76418703079/400000000000 : ℝ), (8252924246919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1786787271/2500000000 : ℝ)|^135 ≤ (4024342233123/6250000000000 : ℝ)^103
        have hw : |(1786787271/2500000000 : ℝ)|=(1786787271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(353546227/1250000000 : ℝ)|^135 ≤ (76418703079/400000000000 : ℝ)^103
        have hw : |(353546227/1250000000 : ℝ)|=(353546227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(316225343/1250000000 : ℝ)|^135 ≤ (8252924246919/50000000000000 : ℝ)^103
        have hw : |(316225343/1250000000 : ℝ)|=(316225343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306063_s4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((13943/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13943/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70189/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70189/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67487/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(67487/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((57957/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57957/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1843/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1843/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56507/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(56507/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (13943/20000 : ℝ) ^ (67/16 : ℝ) ≤ (5519104331720344459/25000000000000000000 : ℝ) := by
    have hpowers : (13943/20000 : ℝ)^67 ≤ (5519104331720344459/25000000000000000000 : ℝ)^16 := by
      have hnat : (13943 : ℕ)^67*25000000000000000000^16 ≤ 5519104331720344459^16*20000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13943 20000 5519104331720344459 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13943/20000 : ℝ)) (X := (5519104331720344459/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (30519104331720344459/25000000000000000000 : ℝ) ≤ (10487891483369761/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (30519104331720344459/25000000000000000000 : ℝ)^16 ≤ (10487891483369761/10000000000000000 : ℝ)^67 := by
      have hnat : (30519104331720344459 : ℕ)^16*10000000000000000^67 ≤ 10487891483369761^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30519104331720344459 25000000000000000000 10487891483369761 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10487891483369761/10000000000000000 : ℝ)) (X := (30519104331720344459/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (18019104331720344459/12500000000000000000 : ℝ) ≤ (2182518435776901/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (18019104331720344459/12500000000000000000 : ℝ)^16 ≤ (2182518435776901/2000000000000000 : ℝ)^67 := by
      have hnat : (18019104331720344459 : ℕ)^16*2000000000000000^67 ≤ 2182518435776901^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18019104331720344459 12500000000000000000 2182518435776901 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2182518435776901/2000000000000000 : ℝ)) (X := (18019104331720344459/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(487891483369761/6971500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(53087586939343/871437500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (13943/20000 : ℝ)) (alpha := (487891483369761/6971500000000000 : ℝ)) (beta := (53087586939343/871437500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13943/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(487891483369761/6971500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(53087586939343/871437500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (70189/100000 : ℝ) ^ (67/16 : ℝ) ≤ (4542361176523632103/20000000000000000000 : ℝ) := by
    have hpowers : (70189/100000 : ℝ)^67 ≤ (4542361176523632103/20000000000000000000 : ℝ)^16 := by
      have hnat : (70189 : ℕ)^67*20000000000000000000^16 ≤ 4542361176523632103^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70189 100000 4542361176523632103 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70189/100000 : ℝ)) (X := (4542361176523632103/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (24542361176523632103/20000000000000000000 : ℝ) ≤ (262522540932403/250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (24542361176523632103/20000000000000000000 : ℝ)^16 ≤ (262522540932403/250000000000000 : ℝ)^67 := by
      have hnat : (24542361176523632103 : ℕ)^16*250000000000000^67 ≤ 262522540932403^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24542361176523632103 20000000000000000000 262522540932403 250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (262522540932403/250000000000000 : ℝ)) (X := (24542361176523632103/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (14542361176523632103/10000000000000000000 : ℝ) ≤ (2733872145345999/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (14542361176523632103/10000000000000000000 : ℝ)^16 ≤ (2733872145345999/2500000000000000 : ℝ)^67 := by
      have hnat : (14542361176523632103 : ℕ)^16*2500000000000000^67 ≤ 2733872145345999^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14542361176523632103 10000000000000000000 2733872145345999 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2733872145345999/2500000000000000 : ℝ)) (X := (14542361176523632103/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(12522540932403/175472500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(108646736021969/1754725000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (70189/100000 : ℝ)) (alpha := (12522540932403/175472500000000 : ℝ)) (beta := (108646736021969/1754725000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (70189/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(12522540932403/175472500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(108646736021969/1754725000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (67487/100000 : ℝ) ^ (67/16 : ℝ) ≤ (4817250973964768027/25000000000000000000 : ℝ) := by
    have hpowers : (67487/100000 : ℝ)^67 ≤ (4817250973964768027/25000000000000000000 : ℝ)^16 := by
      have hnat : (67487 : ℕ)^67*25000000000000000000^16 ≤ 4817250973964768027^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67487 100000 4817250973964768027 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67487/100000 : ℝ)) (X := (4817250973964768027/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (29817250973964768027/25000000000000000000 : ℝ) ≤ (2085956471333349/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (29817250973964768027/25000000000000000000 : ℝ)^16 ≤ (2085956471333349/2000000000000000 : ℝ)^67 := by
      have hnat : (29817250973964768027 : ℕ)^16*2000000000000000^67 ≤ 2085956471333349^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29817250973964768027 25000000000000000000 2085956471333349 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2085956471333349/2000000000000000 : ℝ)) (X := (29817250973964768027/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (17317250973964768027/12500000000000000000 : ℝ) ≤ (10809547334059241/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (17317250973964768027/12500000000000000000 : ℝ)^16 ≤ (10809547334059241/10000000000000000 : ℝ)^67 := by
      have hnat : (17317250973964768027 : ℕ)^16*10000000000000000^67 ≤ 10809547334059241^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17317250973964768027 12500000000000000000 10809547334059241 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10809547334059241/10000000000000000 : ℝ)) (X := (17317250973964768027/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(85956471333349/1349740000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(23735311087031/421793750000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (67487/100000 : ℝ)) (alpha := (85956471333349/1349740000000000 : ℝ)) (beta := (23735311087031/421793750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (67487/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(85956471333349/1349740000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(23735311087031/421793750000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-277608151/2500000000 : ℝ)*X 0 0+(5576235339/10000000000 : ℝ)*X 0 1+(5701377151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((5576980049/10000000000 : ℝ)*X 1 0+(-1121121893/10000000000 : ℝ)*X 1 1+(2847098243/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((112645871/200000000 : ℝ)*X 2 0+(1134995133/2000000000 : ℝ)*X 2 1+(-132656769/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((557472197/1250000000 : ℝ)*X 0 0+(1086774473/2500000000 : ℝ)*X 0 1+(4166188321/10000000000 : ℝ)*X 0 2+(557472197/1250000000 : ℝ)*X 1 0+(1086774473/2500000000 : ℝ)*X 1 1+(4166188321/10000000000 : ℝ)*X 1 2+(557472197/1250000000 : ℝ)*X 2 0+(1086774473/2500000000 : ℝ)*X 2 1+(4166188321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-198254989/2500000000 : ℝ)*X 0 0+(2237040493/5000000000 : ℝ)*X 0 1+(1380961101/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((191486227/400000000 : ℝ)*X 1 0+(-82975309/5000000000 : ℝ)*X 1 1+(689740709/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((4516904939/10000000000 : ℝ)*X 2 0+(7163548821/10000000000 : ℝ)*X 2 1+(-15742637/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((218507763/500000000 : ℝ)*X 0 0+(3125807947/5000000000 : ℝ)*X 0 1+(1003215219/5000000000 : ℝ)*X 0 2+(218507763/500000000 : ℝ)*X 1 0+(3125807947/5000000000 : ℝ)*X 1 1+(1003215219/5000000000 : ℝ)*X 1 2+(218507763/500000000 : ℝ)*X 2 0+(3125807947/5000000000 : ℝ)*X 2 1+(1003215219/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-18111139/1250000000 : ℝ)*X 0 0+(4743605619/10000000000 : ℝ)*X 0 1+(6942666189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((553264083/1250000000 : ℝ)*X 1 0+(-6522563/80000000 : ℝ)*X 1 1+(1387039899/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((1373313959/2000000000 : ℝ)*X 2 0+(2423140663/5000000000 : ℝ)*X 2 1+(-44745901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((700782057/1000000000 : ℝ)*X 0 0+(697301147/2000000000 : ℝ)*X 0 1+(1998581863/10000000000 : ℝ)*X 0 2+(700782057/1000000000 : ℝ)*X 1 0+(697301147/2000000000 : ℝ)*X 1 1+(1998581863/10000000000 : ℝ)*X 1 2+(700782057/1000000000 : ℝ)*X 2 0+(697301147/2000000000 : ℝ)*X 2 1+(1998581863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-623213/62500000 : ℝ)*X 0 0+(6480937679/10000000000 : ℝ)*X 0 1+(1315929611/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((6852785667/10000000000 : ℝ)*X 1 0+(-17554331/2000000000 : ℝ)*X 1 1+(607765603/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((4414744549/10000000000 : ℝ)*X 2 0+(6977717921/10000000000 : ℝ)*X 2 1+(-150194803/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((1786787271/2500000000 : ℝ)*X 0 0+(353546227/1250000000 : ℝ)*X 0 1+(316225343/1250000000 : ℝ)*X 0 2+(1786787271/2500000000 : ℝ)*X 1 0+(353546227/1250000000 : ℝ)*X 1 1+(316225343/1250000000 : ℝ)*X 1 2+(1786787271/2500000000 : ℝ)*X 2 0+(353546227/1250000000 : ℝ)*X 2 1+(316225343/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((57957/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57957/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (158927308377934771452751491/17475807625000000000000000000000 : ℝ) := by norm_num
    linear_combination (19502432743/1000000000000 : ℝ)*(base7) + (894539/1000000000000 : ℝ)*(base50) + (18095921599/125000000000 : ℝ)*(base60) + (3282391858571/1000000000000 : ℝ)*(major_s4_0) + (3282391858571/1000000000000 : ℝ)*(major_s4_1) + (3282391858571/1000000000000 : ℝ)*(major_s4_2) + (2519707/250000000000 : ℝ)*(sp_s4_0) + (482999/200000000000 : ℝ)*(sp_s4_6) + (4423746290027/1000000000000 : ℝ)*(sp_s4_7) + (1105959373417/250000000000 : ℝ)*(sp_s4_8) + (1105959338857/250000000000 : ℝ)*(sp_s4_9) + (537088022897/250000000000 : ℝ)*(sp_s4_13) + (81124813/1000000000000 : ℝ)*(sp_s4_14) + (138241/1000000000000 : ℝ)*(sp_s4_23) + (26610650923/12500000000 : ℝ)*(f.failure) + (1105959373417/250000000000 : ℝ)*(f.sum) + (10669604789988539/62367940000000000000000000000 : ℝ)*base62 + (7055327462209/15550000000000000000000000 : ℝ)*base65 + (422198649052549/501350000000000000000000000 : ℝ)*base67 + (3025438566487/6220000000000000000000000 : ℝ)*base69 + (57975325162697739/2168136500000000000000000000000 : ℝ)*base70 + (2323456538444487/3485750000000000000000000000 : ℝ)*base73 + (8125396888791/100270000000000000000000000 : ℝ)*base74 + (1497117808579619/6971500000000000000000000000 : ℝ)*base76 + (5191020697830387567/17475807625000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (9/156250000000000 : ℝ)*base86 + (9/156250000000000 : ℝ)*base88 + (9/156250000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1843/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1843/3125 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (872715882200685345335332959/235242810250000000000000000000000 : ℝ) := by norm_num
    linear_combination (40609442011/500000000000 : ℝ)*(base7) + (375827/1000000000000 : ℝ)*(base49) + (3142486215137/1000000000000 : ℝ)*(major_s4_0) + (3142486215137/1000000000000 : ℝ)*(major_s4_1) + (3142486215137/1000000000000 : ℝ)*(major_s4_2) + (51753/500000000000 : ℝ)*(sp_s4_0) + (611679/250000000000 : ℝ)*(sp_s4_1) + (5555027/200000000000 : ℝ)*(sp_s4_8) + (1049125781839/250000000000 : ℝ)*(sp_s4_14) + (524559122673/125000000000 : ℝ)*(sp_s4_15) + (1049125800809/250000000000 : ℝ)*(sp_s4_16) + (1059658756687/500000000000 : ℝ)*(sp_s4_20) + (15217/1000000000 : ℝ)*(sp_s4_27) + (2038113846353/1000000000000 : ℝ)*(f.failure) + (1049125800809/250000000000 : ℝ)*(f.sum) + (3727871465061465145127/13533842980000000000000000000000 : ℝ)*base63 + (15104037743197324451/843587500000000000000000000 : ℝ)*base64 + (25516948638755591317/1754725000000000000000000000 : ℝ)*base66 + (319368968526303/1349740000000000000000000000 : ℝ)*base69 + (21021438424195225761/470485620500000000000000000000000 : ℝ)*base70 + (233396498498591/871437500000000000000000000 : ℝ)*base73 + (59900306939339/175472500000000000000000000 : ℝ)*base74 + (1887950359873643/6971500000000000000000000000 : ℝ)*base76 + (3778421811688153309/61165326687500000000000000000000 : ℝ)*base79 + (13813/500000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base82 + (41829/50000000000000000 : ℝ)*base87 + (41829/50000000000000000 : ℝ)*base89 + (41829/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56507/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(56507/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4613034493041693079340474205033/294847457297093750000000000000000000 : ℝ) := by norm_num
    linear_combination (38093193453/500000000000 : ℝ)*(base7) + (31586011491/200000000000 : ℝ)*(base40) + (256513/100000000000 : ℝ)*(base49) + (3000088789703/1000000000000 : ℝ)*(major_s4_0) + (3000088789703/1000000000000 : ℝ)*(major_s4_1) + (3000088789703/1000000000000 : ℝ)*(major_s4_2) + (10113789/500000000000 : ℝ)*(sp_s4_1) + (48890909/1000000000000 : ℝ)*(sp_s4_2) + (10502399/62500000000 : ℝ)*(sp_s4_9) + (31111883/1000000000000 : ℝ)*(sp_s4_20) + (4007178797579/1000000000000 : ℝ)*(sp_s4_21) + (4007158570001/1000000000000 : ℝ)*(sp_s4_22) + (4006961868287/1000000000000 : ℝ)*(sp_s4_23) + (2021914805527/1000000000000 : ℝ)*(sp_s4_27) + (243219941313/125000000000 : ℝ)*(f.failure) + (4007178797579/1000000000000 : ℝ)*(f.sum) + (2269837932962502037/13533842980000000000000000000000 : ℝ)*base63 + (5004605182043/1687175000000000000000000000 : ℝ)*base64 + (1895248864256971/3509450000000000000000000000 : ℝ)*base66 + (118981999437089/1349740000000000000000000000 : ℝ)*base69 + (18940660912220216241/470485620500000000000000000000000 : ℝ)*base71 + (256671579424659/3485750000000000000000000000 : ℝ)*base72 + (297944858347827/701890000000000000000000000 : ℝ)*base74 + (4885065716606967/6971500000000000000000000000 : ℝ)*base76 + (46917391693411719283/122330653375000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (641/6250000000000000 : ℝ)*base86 + (641/6250000000000000 : ℝ)*base88 + (641/6250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((13943/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13943/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70189/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70189/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67487/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(67487/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((57957/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57957/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1843/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1843/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56507/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(56507/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306063_s4 p hpa hpb X hX hprev3

#print axioms solution
