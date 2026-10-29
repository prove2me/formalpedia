-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:00:25.354985+00:00
-- url     : https://prove2.me/submissions/b60502b6-45fe-4e55-bbb5-8f1bbf3bc7cd

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
theorem collision_support_c306083_s1_s1_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-371400087/2000000000 : ℝ)*x 0 + (1262302133/2500000000 : ℝ)*x 1 + (5726631281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (371400087/2000000000 : ℝ)^135 ≤ (11006438298263/100000000000000 : ℝ)^103 := by
    have hnat : (371400087 : ℕ)^135*100000000000000^103 ≤ 11006438298263^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371400087 2000000000 11006438298263 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1262302133/2500000000 : ℝ)^135 ≤ (10208474504371/25000000000000 : ℝ)^103 := by
    have hnat : (1262302133 : ℕ)^135*25000000000000^103 ≤ 10208474504371^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262302133 2500000000 10208474504371 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5726631281/10000000000 : ℝ)^135 ≤ (48159663668023/100000000000000 : ℝ)^103 := by
    have hnat : (5726631281 : ℕ)^135*100000000000000^103 ≤ 48159663668023^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5726631281 10000000000 48159663668023 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-371400087/2000000000 : ℝ), (1262302133/2500000000 : ℝ), (5726631281/10000000000 : ℝ)] ![(11006438298263/100000000000000 : ℝ), (10208474504371/25000000000000 : ℝ), (48159663668023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-371400087/2000000000 : ℝ)|^135 ≤ (11006438298263/100000000000000 : ℝ)^103
        have hw : |(-371400087/2000000000 : ℝ)|=(371400087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1262302133/2500000000 : ℝ)|^135 ≤ (10208474504371/25000000000000 : ℝ)^103
        have hw : |(1262302133/2500000000 : ℝ)|=(1262302133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5726631281/10000000000 : ℝ)|^135 ≤ (48159663668023/100000000000000 : ℝ)^103
        have hw : |(5726631281/10000000000 : ℝ)|=(5726631281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3550919111/10000000000 : ℝ)*x 0 + (1392782639/2000000000 : ℝ)*x 1 + (-1986554559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3550919111/10000000000 : ℝ)^135 ≤ (25741913536409/100000000000000 : ℝ)^103 := by
    have hnat : (3550919111 : ℕ)^135*100000000000000^103 ≤ 25741913536409^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3550919111 10000000000 25741913536409 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1392782639/2000000000 : ℝ)^135 ≤ (6223448334661/10000000000000 : ℝ)^103 := by
    have hnat : (1392782639 : ℕ)^135*10000000000000^103 ≤ 6223448334661^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392782639 2000000000 6223448334661 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1986554559/10000000000 : ℝ)^135 ≤ (12023603110177/100000000000000 : ℝ)^103 := by
    have hnat : (1986554559 : ℕ)^135*100000000000000^103 ≤ 12023603110177^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986554559 10000000000 12023603110177 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3550919111/10000000000 : ℝ), (1392782639/2000000000 : ℝ), (-1986554559/10000000000 : ℝ)] ![(25741913536409/100000000000000 : ℝ), (6223448334661/10000000000000 : ℝ), (12023603110177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3550919111/10000000000 : ℝ)|^135 ≤ (25741913536409/100000000000000 : ℝ)^103
        have hw : |(3550919111/10000000000 : ℝ)|=(3550919111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1392782639/2000000000 : ℝ)|^135 ≤ (6223448334661/10000000000000 : ℝ)^103
        have hw : |(1392782639/2000000000 : ℝ)|=(1392782639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1986554559/10000000000 : ℝ)|^135 ≤ (12023603110177/100000000000000 : ℝ)^103
        have hw : |(-1986554559/10000000000 : ℝ)|=(1986554559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (637150151/2000000000 : ℝ)*x 0 + (582187711/1250000000 : ℝ)*x 1 + (2529517899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (637150151/2000000000 : ℝ)^135 ≤ (11164514249463/50000000000000 : ℝ)^103 := by
    have hnat : (637150151 : ℕ)^135*50000000000000^103 ≤ 11164514249463^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637150151 2000000000 11164514249463 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (582187711/1250000000 : ℝ)^135 ≤ (18366437900117/50000000000000 : ℝ)^103 := by
    have hnat : (582187711 : ℕ)^135*50000000000000^103 ≤ 18366437900117^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582187711 1250000000 18366437900117 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2529517899/5000000000 : ℝ)^135 ≤ (20469047844351/50000000000000 : ℝ)^103 := by
    have hnat : (2529517899 : ℕ)^135*50000000000000^103 ≤ 20469047844351^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2529517899 5000000000 20469047844351 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(637150151/2000000000 : ℝ), (582187711/1250000000 : ℝ), (2529517899/5000000000 : ℝ)] ![(11164514249463/50000000000000 : ℝ), (18366437900117/50000000000000 : ℝ), (20469047844351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(637150151/2000000000 : ℝ)|^135 ≤ (11164514249463/50000000000000 : ℝ)^103
        have hw : |(637150151/2000000000 : ℝ)|=(637150151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(582187711/1250000000 : ℝ)|^135 ≤ (18366437900117/50000000000000 : ℝ)^103
        have hw : |(582187711/1250000000 : ℝ)|=(582187711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2529517899/5000000000 : ℝ)|^135 ≤ (20469047844351/50000000000000 : ℝ)^103
        have hw : |(2529517899/5000000000 : ℝ)|=(2529517899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-261222497/1000000000 : ℝ)*x 0 + (1789665409/5000000000 : ℝ)*x 1 + (3246329687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261222497/1000000000 : ℝ)^135 ≤ (3442846376859/20000000000000 : ℝ)^103 := by
    have hnat : (261222497 : ℕ)^135*20000000000000^103 ≤ 3442846376859^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261222497 1000000000 3442846376859 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1789665409/5000000000 : ℝ)^135 ≤ (3251525629247/12500000000000 : ℝ)^103 := by
    have hnat : (1789665409 : ℕ)^135*12500000000000^103 ≤ 3251525629247^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789665409 5000000000 3251525629247 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3246329687/5000000000 : ℝ)^135 ≤ (56773563066513/100000000000000 : ℝ)^103 := by
    have hnat : (3246329687 : ℕ)^135*100000000000000^103 ≤ 56773563066513^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3246329687 5000000000 56773563066513 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261222497/1000000000 : ℝ), (1789665409/5000000000 : ℝ), (3246329687/5000000000 : ℝ)] ![(3442846376859/20000000000000 : ℝ), (3251525629247/12500000000000 : ℝ), (56773563066513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261222497/1000000000 : ℝ)|^135 ≤ (3442846376859/20000000000000 : ℝ)^103
        have hw : |(-261222497/1000000000 : ℝ)|=(261222497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1789665409/5000000000 : ℝ)|^135 ≤ (3251525629247/12500000000000 : ℝ)^103
        have hw : |(1789665409/5000000000 : ℝ)|=(1789665409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3246329687/5000000000 : ℝ)|^135 ≤ (56773563066513/100000000000000 : ℝ)^103
        have hw : |(3246329687/5000000000 : ℝ)|=(3246329687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1415310011/2500000000 : ℝ)*x 0 + (14120891/2500000000 : ℝ)*x 1 + (3055803991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1415310011/2500000000 : ℝ)^135 ≤ (5930021192607/12500000000000 : ℝ)^103 := by
    have hnat : (1415310011 : ℕ)^135*12500000000000^103 ≤ 5930021192607^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415310011 2500000000 5930021192607 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14120891/2500000000 : ℝ)^135 ≤ (14138395741/12500000000000 : ℝ)^103 := by
    have hnat : (14120891 : ℕ)^135*12500000000000^103 ≤ 14138395741^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14120891 2500000000 14138395741 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3055803991/5000000000 : ℝ)^135 ≤ (26223361641313/50000000000000 : ℝ)^103 := by
    have hnat : (3055803991 : ℕ)^135*50000000000000^103 ≤ 26223361641313^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3055803991 5000000000 26223361641313 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1415310011/2500000000 : ℝ), (14120891/2500000000 : ℝ), (3055803991/5000000000 : ℝ)] ![(5930021192607/12500000000000 : ℝ), (14138395741/12500000000000 : ℝ), (26223361641313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1415310011/2500000000 : ℝ)|^135 ≤ (5930021192607/12500000000000 : ℝ)^103
        have hw : |(1415310011/2500000000 : ℝ)|=(1415310011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14120891/2500000000 : ℝ)|^135 ≤ (14138395741/12500000000000 : ℝ)^103
        have hw : |(14120891/2500000000 : ℝ)|=(14120891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3055803991/5000000000 : ℝ)|^135 ≤ (26223361641313/50000000000000 : ℝ)^103
        have hw : |(3055803991/5000000000 : ℝ)|=(3055803991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1339782969/10000000000 : ℝ)*x 0 + (2185656313/2500000000 : ℝ)*x 1 + (-397270459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339782969/10000000000 : ℝ)^135 ≤ (224218724321/3125000000000 : ℝ)^103 := by
    have hnat : (1339782969 : ℕ)^135*3125000000000^103 ≤ 224218724321^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339782969 10000000000 224218724321 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185656313/2500000000 : ℝ)^135 ≤ (41925783173729/50000000000000 : ℝ)^103 := by
    have hnat : (2185656313 : ℕ)^135*50000000000000^103 ≤ 41925783173729^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185656313 2500000000 41925783173729 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397270459/2500000000 : ℝ)^135 ≤ (1794686890699/20000000000000 : ℝ)^103 := by
    have hnat : (397270459 : ℕ)^135*20000000000000^103 ≤ 1794686890699^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397270459 2500000000 1794686890699 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339782969/10000000000 : ℝ), (2185656313/2500000000 : ℝ), (-397270459/2500000000 : ℝ)] ![(224218724321/3125000000000 : ℝ), (41925783173729/50000000000000 : ℝ), (1794686890699/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339782969/10000000000 : ℝ)|^135 ≤ (224218724321/3125000000000 : ℝ)^103
        have hw : |(1339782969/10000000000 : ℝ)|=(1339782969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2185656313/2500000000 : ℝ)|^135 ≤ (41925783173729/50000000000000 : ℝ)^103
        have hw : |(2185656313/2500000000 : ℝ)|=(2185656313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397270459/2500000000 : ℝ)|^135 ≤ (1794686890699/20000000000000 : ℝ)^103
        have hw : |(-397270459/2500000000 : ℝ)|=(397270459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2715417179/10000000000 : ℝ)*x 0 + (763206581/1250000000 : ℝ)*x 1 + (788185281/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2715417179/10000000000 : ℝ)^135 ≤ (18110945510523/100000000000000 : ℝ)^103 := by
    have hnat : (2715417179 : ℕ)^135*100000000000000^103 ≤ 18110945510523^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715417179 10000000000 18110945510523 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (763206581/1250000000 : ℝ)^135 ≤ (10475950055701/20000000000000 : ℝ)^103 := by
    have hnat : (763206581 : ℕ)^135*20000000000000^103 ≤ 10475950055701^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763206581 1250000000 10475950055701 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788185281/2000000000 : ℝ)^135 ≤ (29509304190821/100000000000000 : ℝ)^103 := by
    have hnat : (788185281 : ℕ)^135*100000000000000^103 ≤ 29509304190821^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788185281 2000000000 29509304190821 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2715417179/10000000000 : ℝ), (763206581/1250000000 : ℝ), (788185281/2000000000 : ℝ)] ![(18110945510523/100000000000000 : ℝ), (10475950055701/20000000000000 : ℝ), (29509304190821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2715417179/10000000000 : ℝ)|^135 ≤ (18110945510523/100000000000000 : ℝ)^103
        have hw : |(2715417179/10000000000 : ℝ)|=(2715417179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(763206581/1250000000 : ℝ)|^135 ≤ (10475950055701/20000000000000 : ℝ)^103
        have hw : |(763206581/1250000000 : ℝ)|=(763206581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(788185281/2000000000 : ℝ)|^135 ≤ (29509304190821/100000000000000 : ℝ)^103
        have hw : |(788185281/2000000000 : ℝ)|=(788185281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-227035457/5000000000 : ℝ)*x 0 + (1315064541/5000000000 : ℝ)*x 1 + (4253157303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227035457/5000000000 : ℝ)^135 ≤ (434369576883/25000000000000 : ℝ)^103 := by
    have hnat : (227035457 : ℕ)^135*25000000000000^103 ≤ 434369576883^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227035457 5000000000 434369576883 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315064541/5000000000 : ℝ)^135 ≤ (434225947397/2500000000000 : ℝ)^103 := by
    have hnat : (1315064541 : ℕ)^135*2500000000000^103 ≤ 434225947397^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315064541 5000000000 434225947397 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4253157303/5000000000 : ℝ)^135 ≤ (80893483777493/100000000000000 : ℝ)^103 := by
    have hnat : (4253157303 : ℕ)^135*100000000000000^103 ≤ 80893483777493^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253157303 5000000000 80893483777493 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-227035457/5000000000 : ℝ), (1315064541/5000000000 : ℝ), (4253157303/5000000000 : ℝ)] ![(434369576883/25000000000000 : ℝ), (434225947397/2500000000000 : ℝ), (80893483777493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-227035457/5000000000 : ℝ)|^135 ≤ (434369576883/25000000000000 : ℝ)^103
        have hw : |(-227035457/5000000000 : ℝ)|=(227035457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315064541/5000000000 : ℝ)|^135 ≤ (434225947397/2500000000000 : ℝ)^103
        have hw : |(1315064541/5000000000 : ℝ)|=(1315064541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4253157303/5000000000 : ℝ)|^135 ≤ (80893483777493/100000000000000 : ℝ)^103
        have hw : |(4253157303/5000000000 : ℝ)|=(4253157303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8944908027/10000000000 : ℝ)*x 0 + (482757/5000000000 : ℝ)*x 1 + (1090920051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8944908027/10000000000 : ℝ)^135 ≤ (3456141252593/4000000000000 : ℝ)^103 := by
    have hnat : (8944908027 : ℕ)^135*4000000000000^103 ≤ 3456141252593^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8944908027 10000000000 3456141252593 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482757/5000000000 : ℝ)^135 ≤ (273070593/50000000000000 : ℝ)^103 := by
    have hnat : (482757 : ℕ)^135*50000000000000^103 ≤ 273070593^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482757 5000000000 273070593 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090920051/5000000000 : ℝ)^135 ≤ (13595922529067/100000000000000 : ℝ)^103 := by
    have hnat : (1090920051 : ℕ)^135*100000000000000^103 ≤ 13595922529067^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090920051 5000000000 13595922529067 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8944908027/10000000000 : ℝ), (482757/5000000000 : ℝ), (1090920051/5000000000 : ℝ)] ![(3456141252593/4000000000000 : ℝ), (273070593/50000000000000 : ℝ), (13595922529067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8944908027/10000000000 : ℝ)|^135 ≤ (3456141252593/4000000000000 : ℝ)^103
        have hw : |(8944908027/10000000000 : ℝ)|=(8944908027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(482757/5000000000 : ℝ)|^135 ≤ (273070593/50000000000000 : ℝ)^103
        have hw : |(482757/5000000000 : ℝ)|=(482757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090920051/5000000000 : ℝ)|^135 ≤ (13595922529067/100000000000000 : ℝ)^103
        have hw : |(1090920051/5000000000 : ℝ)|=(1090920051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2473490511/5000000000 : ℝ)*x 0 + (1267810573/2000000000 : ℝ)*x 1 + (-1052090161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2473490511/5000000000 : ℝ)^135 ≤ (4969217466827/12500000000000 : ℝ)^103 := by
    have hnat : (2473490511 : ℕ)^135*12500000000000^103 ≤ 4969217466827^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2473490511 5000000000 4969217466827 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1267810573/2000000000 : ℝ)^135 ≤ (27509797099647/50000000000000 : ℝ)^103 := by
    have hnat : (1267810573 : ℕ)^135*50000000000000^103 ≤ 27509797099647^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267810573 2000000000 27509797099647 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052090161/10000000000 : ℝ)^135 ≤ (5226666048881/100000000000000 : ℝ)^103 := by
    have hnat : (1052090161 : ℕ)^135*100000000000000^103 ≤ 5226666048881^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052090161 10000000000 5226666048881 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2473490511/5000000000 : ℝ), (1267810573/2000000000 : ℝ), (-1052090161/10000000000 : ℝ)] ![(4969217466827/12500000000000 : ℝ), (27509797099647/50000000000000 : ℝ), (5226666048881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2473490511/5000000000 : ℝ)|^135 ≤ (4969217466827/12500000000000 : ℝ)^103
        have hw : |(2473490511/5000000000 : ℝ)|=(2473490511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1267810573/2000000000 : ℝ)|^135 ≤ (27509797099647/50000000000000 : ℝ)^103
        have hw : |(1267810573/2000000000 : ℝ)|=(1267810573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052090161/10000000000 : ℝ)|^135 ≤ (5226666048881/100000000000000 : ℝ)^103
        have hw : |(-1052090161/10000000000 : ℝ)|=(1052090161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2907087757/10000000000 : ℝ)*x 0 + (1586955019/5000000000 : ℝ)*x 1 + (6597237103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2907087757/10000000000 : ℝ)^135 ≤ (19804574957687/100000000000000 : ℝ)^103 := by
    have hnat : (2907087757 : ℕ)^135*100000000000000^103 ≤ 19804574957687^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2907087757 10000000000 19804574957687 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1586955019/5000000000 : ℝ)^135 ≤ (5555078870643/25000000000000 : ℝ)^103 := by
    have hnat : (1586955019 : ℕ)^135*25000000000000^103 ≤ 5555078870643^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586955019 5000000000 5555078870643 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6597237103/10000000000 : ℝ)^135 ≤ (28987554773443/50000000000000 : ℝ)^103 := by
    have hnat : (6597237103 : ℕ)^135*50000000000000^103 ≤ 28987554773443^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6597237103 10000000000 28987554773443 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2907087757/10000000000 : ℝ), (1586955019/5000000000 : ℝ), (6597237103/10000000000 : ℝ)] ![(19804574957687/100000000000000 : ℝ), (5555078870643/25000000000000 : ℝ), (28987554773443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2907087757/10000000000 : ℝ)|^135 ≤ (19804574957687/100000000000000 : ℝ)^103
        have hw : |(2907087757/10000000000 : ℝ)|=(2907087757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1586955019/5000000000 : ℝ)|^135 ≤ (5555078870643/25000000000000 : ℝ)^103
        have hw : |(1586955019/5000000000 : ℝ)|=(1586955019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6597237103/10000000000 : ℝ)|^135 ≤ (28987554773443/50000000000000 : ℝ)^103
        have hw : |(6597237103/10000000000 : ℝ)|=(6597237103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1443504037/10000000000 : ℝ)*x 0 + (828903253/1250000000 : ℝ)*x 1 + (4363249251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1443504037/10000000000 : ℝ)^135 ≤ (7911636298671/100000000000000 : ℝ)^103 := by
    have hnat : (1443504037 : ℕ)^135*100000000000000^103 ≤ 7911636298671^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1443504037 10000000000 7911636298671 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (828903253/1250000000 : ℝ)^135 ≤ (466935247477/800000000000 : ℝ)^103 := by
    have hnat : (828903253 : ℕ)^135*800000000000^103 ≤ 466935247477^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828903253 1250000000 466935247477 800000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4363249251/10000000000 : ℝ)^135 ≤ (8430364438099/25000000000000 : ℝ)^103 := by
    have hnat : (4363249251 : ℕ)^135*25000000000000^103 ≤ 8430364438099^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363249251 10000000000 8430364438099 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1443504037/10000000000 : ℝ), (828903253/1250000000 : ℝ), (4363249251/10000000000 : ℝ)] ![(7911636298671/100000000000000 : ℝ), (466935247477/800000000000 : ℝ), (8430364438099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1443504037/10000000000 : ℝ)|^135 ≤ (7911636298671/100000000000000 : ℝ)^103
        have hw : |(-1443504037/10000000000 : ℝ)|=(1443504037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(828903253/1250000000 : ℝ)|^135 ≤ (466935247477/800000000000 : ℝ)^103
        have hw : |(828903253/1250000000 : ℝ)|=(828903253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4363249251/10000000000 : ℝ)|^135 ≤ (8430364438099/25000000000000 : ℝ)^103
        have hw : |(4363249251/10000000000 : ℝ)|=(4363249251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8620647097/10000000000 : ℝ)*x 0 + (2406949/5000000000 : ℝ)*x 1 + (333160991/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8620647097/10000000000 : ℝ)^135 ≤ (257254771847/312500000000 : ℝ)^103 := by
    have hnat : (8620647097 : ℕ)^135*312500000000^103 ≤ 257254771847^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8620647097 10000000000 257254771847 312500000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406949/5000000000 : ℝ)^135 ≤ (4485556219/100000000000000 : ℝ)^103 := by
    have hnat : (2406949 : ℕ)^135*100000000000000^103 ≤ 4485556219^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406949 5000000000 4485556219 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333160991/1250000000 : ℝ)^135 ≤ (8836993724461/50000000000000 : ℝ)^103 := by
    have hnat : (333160991 : ℕ)^135*50000000000000^103 ≤ 8836993724461^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333160991 1250000000 8836993724461 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8620647097/10000000000 : ℝ), (2406949/5000000000 : ℝ), (333160991/1250000000 : ℝ)] ![(257254771847/312500000000 : ℝ), (4485556219/100000000000000 : ℝ), (8836993724461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8620647097/10000000000 : ℝ)|^135 ≤ (257254771847/312500000000 : ℝ)^103
        have hw : |(8620647097/10000000000 : ℝ)|=(8620647097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2406949/5000000000 : ℝ)|^135 ≤ (4485556219/100000000000000 : ℝ)^103
        have hw : |(2406949/5000000000 : ℝ)|=(2406949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(333160991/1250000000 : ℝ)|^135 ≤ (8836993724461/50000000000000 : ℝ)^103
        have hw : |(333160991/1250000000 : ℝ)|=(333160991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (208931457/1000000000 : ℝ)*x 0 + (7985368443/10000000000 : ℝ)*x 1 + (-2021726/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208931457/1000000000 : ℝ)^135 ≤ (6422629830177/50000000000000 : ℝ)^103 := by
    have hnat : (208931457 : ℕ)^135*50000000000000^103 ≤ 6422629830177^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208931457 1000000000 6422629830177 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7985368443/10000000000 : ℝ)^135 ≤ (1163482943733/1562500000000 : ℝ)^103 := by
    have hnat : (7985368443 : ℕ)^135*1562500000000^103 ≤ 1163482943733^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7985368443 10000000000 1163482943733 1562500000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021726/9765625 : ℝ)^135 ≤ (2538366384297/20000000000000 : ℝ)^103 := by
    have hnat : (2021726 : ℕ)^135*20000000000000^103 ≤ 2538366384297^103*9765625^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021726 9765625 2538366384297 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208931457/1000000000 : ℝ), (7985368443/10000000000 : ℝ), (-2021726/9765625 : ℝ)] ![(6422629830177/50000000000000 : ℝ), (1163482943733/1562500000000 : ℝ), (2538366384297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208931457/1000000000 : ℝ)|^135 ≤ (6422629830177/50000000000000 : ℝ)^103
        have hw : |(208931457/1000000000 : ℝ)|=(208931457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7985368443/10000000000 : ℝ)|^135 ≤ (1163482943733/1562500000000 : ℝ)^103
        have hw : |(7985368443/10000000000 : ℝ)|=(7985368443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2021726/9765625 : ℝ)|^135 ≤ (2538366384297/20000000000000 : ℝ)^103
        have hw : |(-2021726/9765625 : ℝ)|=(2021726/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306083_s1_s1_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (78127047/125000000 : ℝ)*x 0 + (710287431/2000000000 : ℝ)*x 1 + (2956012469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (78127047/125000000 : ℝ)^135 ≤ (2160424063927/4000000000000 : ℝ)^103 := by
    have hnat : (78127047 : ℕ)^135*4000000000000^103 ≤ 2160424063927^103*125000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78127047 125000000 2160424063927 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (710287431/2000000000 : ℝ)^135 ≤ (12873417946553/50000000000000 : ℝ)^103 := by
    have hnat : (710287431 : ℕ)^135*50000000000000^103 ≤ 12873417946553^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710287431 2000000000 12873417946553 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956012469/10000000000 : ℝ)^135 ≤ (10121281243607/50000000000000 : ℝ)^103 := by
    have hnat : (2956012469 : ℕ)^135*50000000000000^103 ≤ 10121281243607^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956012469 10000000000 10121281243607 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(78127047/125000000 : ℝ), (710287431/2000000000 : ℝ), (2956012469/10000000000 : ℝ)] ![(2160424063927/4000000000000 : ℝ), (12873417946553/50000000000000 : ℝ), (10121281243607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(78127047/125000000 : ℝ)|^135 ≤ (2160424063927/4000000000000 : ℝ)^103
        have hw : |(78127047/125000000 : ℝ)|=(78127047/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(710287431/2000000000 : ℝ)|^135 ≤ (12873417946553/50000000000000 : ℝ)^103
        have hw : |(710287431/2000000000 : ℝ)|=(710287431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2956012469/10000000000 : ℝ)|^135 ≤ (10121281243607/50000000000000 : ℝ)^103
        have hw : |(2956012469/10000000000 : ℝ)|=(2956012469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306083_s1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((16411/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16411/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((87423/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(87423/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91599/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(91599/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((65139/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(65139/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((66541/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(66541/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4631/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4631/6250 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
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
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (16411/20000 : ℝ) ^ (67/16 : ℝ) ≤ (8736649075298505109/20000000000000000000 : ℝ) := by
    have hpowers : (16411/20000 : ℝ)^67 ≤ (8736649075298505109/20000000000000000000 : ℝ)^16 := by
      have hnat : (16411 : ℕ)^67*20000000000000000000^16 ≤ 8736649075298505109^16*20000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16411 20000 8736649075298505109 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16411/20000 : ℝ)) (X := (8736649075298505109/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (28736649075298505109/20000000000000000000 : ℝ) ≤ (5452046203833711/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (28736649075298505109/20000000000000000000 : ℝ)^16 ≤ (5452046203833711/5000000000000000 : ℝ)^67 := by
      have hnat : (28736649075298505109 : ℕ)^16*5000000000000000^67 ≤ 5452046203833711^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28736649075298505109 20000000000000000000 5452046203833711 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5452046203833711/5000000000000000 : ℝ)) (X := (28736649075298505109/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (18736649075298505109/10000000000000000000 : ℝ) ≤ (11617708066395203/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (18736649075298505109/10000000000000000000 : ℝ)^16 ≤ (11617708066395203/10000000000000000 : ℝ)^67 := by
      have hnat : (18736649075298505109 : ℕ)^16*10000000000000000^67 ≤ 11617708066395203^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18736649075298505109 10000000000000000000 11617708066395203 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11617708066395203/10000000000000000 : ℝ)) (X := (18736649075298505109/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(452046203833711/4102750000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(713615658727781/8205500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (16411/20000 : ℝ)) (alpha := (452046203833711/4102750000000000 : ℝ)) (beta := (713615658727781/8205500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16411/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(452046203833711/4102750000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(713615658727781/8205500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (87423/100000 : ℝ) ^ (67/16 : ℝ) ≤ (28479190892339105319/50000000000000000000 : ℝ) := by
    have hpowers : (87423/100000 : ℝ)^67 ≤ (28479190892339105319/50000000000000000000 : ℝ)^16 := by
      have hnat : (87423 : ℕ)^67*50000000000000000000^16 ≤ 28479190892339105319^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87423 100000 28479190892339105319 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87423/100000 : ℝ)) (X := (28479190892339105319/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (78479190892339105319/50000000000000000000 : ℝ) ≤ (2227329689664539/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (78479190892339105319/50000000000000000000 : ℝ)^16 ≤ (2227329689664539/2000000000000000 : ℝ)^67 := by
      have hnat : (78479190892339105319 : ℕ)^16*2000000000000000^67 ≤ 2227329689664539^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78479190892339105319 50000000000000000000 2227329689664539 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2227329689664539/2000000000000000 : ℝ)) (X := (78479190892339105319/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (53479190892339105319/25000000000000000000 : ℝ) ≤ (11991249364813149/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (53479190892339105319/25000000000000000000 : ℝ)^16 ≤ (11991249364813149/10000000000000000 : ℝ)^67 := by
      have hnat : (53479190892339105319 : ℕ)^16*10000000000000000^67 ≤ 11991249364813149^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53479190892339105319 25000000000000000000 11991249364813149 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11991249364813149/10000000000000000 : ℝ)) (X := (53479190892339105319/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(10825223317359/83260000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(61042922606461/624450000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (87423/100000 : ℝ)) (alpha := (10825223317359/83260000000000 : ℝ)) (beta := (61042922606461/624450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (87423/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(10825223317359/83260000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(61042922606461/624450000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (91599/100000 : ℝ) ^ (67/16 : ℝ) ≤ (34624813785201792527/50000000000000000000 : ℝ) := by
    have hpowers : (91599/100000 : ℝ)^67 ≤ (34624813785201792527/50000000000000000000 : ℝ)^16 := by
      have hnat : (91599 : ℕ)^67*50000000000000000000^16 ≤ 34624813785201792527^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91599 100000 34624813785201792527 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91599/100000 : ℝ)) (X := (34624813785201792527/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (84624813785201792527/50000000000000000000 : ℝ) ≤ (11338974647986887/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (84624813785201792527/50000000000000000000 : ℝ)^16 ≤ (11338974647986887/10000000000000000 : ℝ)^67 := by
      have hnat : (84624813785201792527 : ℕ)^16*10000000000000000^67 ≤ 11338974647986887^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84624813785201792527 50000000000000000000 11338974647986887 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11338974647986887/10000000000000000 : ℝ)) (X := (84624813785201792527/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (59624813785201792527/25000000000000000000 : ℝ) ≤ (1230682870164529/1000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (59624813785201792527/25000000000000000000 : ℝ)^16 ≤ (1230682870164529/1000000000000000 : ℝ)^67 := by
      have hnat : (59624813785201792527 : ℕ)^16*1000000000000000^67 ≤ 1230682870164529^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59624813785201792527 25000000000000000000 1230682870164529 1000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1230682870164529/1000000000000000 : ℝ)) (X := (59624813785201792527/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1338974647986887/9159900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(967854053658403/9159900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (91599/100000 : ℝ)) (alpha := (1338974647986887/9159900000000000 : ℝ)) (beta := (967854053658403/9159900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (91599/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1338974647986887/9159900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(967854053658403/9159900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-371400087/2000000000 : ℝ)*X 0 0+(1262302133/2500000000 : ℝ)*X 0 1+(5726631281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3550919111/10000000000 : ℝ)*X 2 0+(1392782639/2000000000 : ℝ)*X 2 1+(-1986554559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((637150151/2000000000 : ℝ)*X 0 0+(582187711/1250000000 : ℝ)*X 0 1+(2529517899/5000000000 : ℝ)*X 0 2+(637150151/2000000000 : ℝ)*X 1 0+(582187711/1250000000 : ℝ)*X 1 1+(2529517899/5000000000 : ℝ)*X 1 2+(637150151/2000000000 : ℝ)*X 2 0+(582187711/1250000000 : ℝ)*X 2 1+(2529517899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-261222497/1000000000 : ℝ)*X 0 0+(1789665409/5000000000 : ℝ)*X 0 1+(3246329687/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1415310011/2500000000 : ℝ)*X 1 0+(14120891/2500000000 : ℝ)*X 1 1+(3055803991/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1339782969/10000000000 : ℝ)*X 2 0+(2185656313/2500000000 : ℝ)*X 2 1+(-397270459/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2715417179/10000000000 : ℝ)*X 0 0+(763206581/1250000000 : ℝ)*X 0 1+(788185281/2000000000 : ℝ)*X 0 2+(2715417179/10000000000 : ℝ)*X 1 0+(763206581/1250000000 : ℝ)*X 1 1+(788185281/2000000000 : ℝ)*X 1 2+(2715417179/10000000000 : ℝ)*X 2 0+(763206581/1250000000 : ℝ)*X 2 1+(788185281/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-227035457/5000000000 : ℝ)*X 0 0+(1315064541/5000000000 : ℝ)*X 0 1+(4253157303/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((8944908027/10000000000 : ℝ)*X 1 0+(482757/5000000000 : ℝ)*X 1 1+(1090920051/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2473490511/5000000000 : ℝ)*X 2 0+(1267810573/2000000000 : ℝ)*X 2 1+(-1052090161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2907087757/10000000000 : ℝ)*X 0 0+(1586955019/5000000000 : ℝ)*X 0 1+(6597237103/10000000000 : ℝ)*X 0 2+(2907087757/10000000000 : ℝ)*X 1 0+(1586955019/5000000000 : ℝ)*X 1 1+(6597237103/10000000000 : ℝ)*X 1 2+(2907087757/10000000000 : ℝ)*X 2 0+(1586955019/5000000000 : ℝ)*X 2 1+(6597237103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1443504037/10000000000 : ℝ)*X 0 0+(828903253/1250000000 : ℝ)*X 0 1+(4363249251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((8620647097/10000000000 : ℝ)*X 1 0+(2406949/5000000000 : ℝ)*X 1 1+(333160991/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((208931457/1000000000 : ℝ)*X 2 0+(7985368443/10000000000 : ℝ)*X 2 1+(-2021726/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((78127047/125000000 : ℝ)*X 0 0+(710287431/2000000000 : ℝ)*X 0 1+(2956012469/10000000000 : ℝ)*X 0 2+(78127047/125000000 : ℝ)*X 1 0+(710287431/2000000000 : ℝ)*X 1 1+(2956012469/10000000000 : ℝ)*X 1 2+(78127047/125000000 : ℝ)*X 2 0+(710287431/2000000000 : ℝ)*X 2 1+(2956012469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((65139/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(65139/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2519562727580911051980546334543/521495953317250000000000000000000000 : ℝ) := by norm_num
    linear_combination (727021605533/1000000000000 : ℝ)*(base7) + (5008761/1000000000000 : ℝ)*(base23) + (19990128837/62500000000 : ℝ)*(base49) + (176845062991/1000000000000 : ℝ)*(base60) + (2033243265767/1000000000000 : ℝ)*(major_s1_0) + (2033243265767/1000000000000 : ℝ)*(major_s1_1) + (2033243265767/1000000000000 : ℝ)*(major_s1_2) + (8726973/500000000000 : ℝ)*(sp_s1_0) + (1620099/200000000000 : ℝ)*(sp_s1_6) + (2297027333373/1000000000000 : ℝ)*(sp_s1_7) + (574262735211/250000000000 : ℝ)*(sp_s1_8) + (2297045932083/1000000000000 : ℝ)*(sp_s1_9) + (409141726051/200000000000 : ℝ)*(sp_s1_13) + (1538381/250000000000 : ℝ)*(sp_s1_14) + (1318695125217/1000000000000 : ℝ)*(f.failure) + (574262735211/250000000000 : ℝ)*(f.sum) + (602110585611789247/2542177580000000000000000000000 : ℝ)*base63 + (1787718470852359/9159900000000000000000000000 : ℝ)*base64 + (37556316194171/83260000000000000000000000 : ℝ)*base67 + (2017277774816389/9159900000000000000000000000 : ℝ)*base69 + (272550728659042177919/751615594500000000000000000000000 : ℝ)*base70 + (1532475553138123/8205500000000000000000000000 : ℝ)*base72 + (21707848462313/156112500000000000000000000 : ℝ)*base74 + (1568495050885563/4102750000000000000000000000 : ℝ)*base76 + (2353105580558288713/17079748250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (4181/50000000000000000 : ℝ)*base87 + (4181/50000000000000000 : ℝ)*base89 + (4181/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((66541/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(66541/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1384615675710015143470565406561/260747976658625000000000000000000000 : ℝ) := by norm_num
    linear_combination (447104774783/1000000000000 : ℝ)*(base7) + (2741263/250000000000 : ℝ)*(base33) + (265698062581/500000000000 : ℝ)*(base40) + (25521636513/250000000000 : ℝ)*(base49) + (41025484753/100000000000 : ℝ)*(base60) + (2102729154991/1000000000000 : ℝ)*(major_s1_0) + (2102740120043/1000000000000 : ℝ)*(major_s1_1) + (2102740120043/1000000000000 : ℝ)*(major_s1_2) + (2922251/250000000000 : ℝ)*(sp_s1_2) + (1282256969187/500000000000 : ℝ)*(sp_s1_14) + (1282205063727/500000000000 : ℝ)*(sp_s1_15) + (2564491284317/1000000000000 : ℝ)*(sp_s1_16) + (362174657633/200000000000 : ℝ)*(sp_s1_20) + (23211467/250000000000 : ℝ)*(sp_s1_22) + (681884256691/500000000000 : ℝ)*(f.failure) + (1282256969187/500000000000 : ℝ)*(f.sum) + (779952749946266409/2542177580000000000000000000000 : ℝ)*base63 + (4555501062607291/9159900000000000000000000000 : ℝ)*base64 + (19983641169877/83260000000000000000000000 : ℝ)*base66 + (1046505034824269/9159900000000000000000000000 : ℝ)*base68 + (429967616657968299407/751615594500000000000000000000000 : ℝ)*base70 + (812820199471121/8205500000000000000000000000 : ℝ)*base73 + (126965654248721/312225000000000000000000000 : ℝ)*base75 + (162478549892131/1025687500000000000000000000 : ℝ)*base76 + (2774112681169334287/8539874125000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (4263/25000000000000000 : ℝ)*base87 + (4263/25000000000000000 : ℝ)*base89 + (4263/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4631/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4631/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (860748114703377831502397449/125269265750000000000000000000000 : ℝ) := by norm_num
    linear_combination (406455643709/500000000000 : ℝ)*(base7) + (1859991/500000000000 : ℝ)*(base11) + (40190558159/125000000000 : ℝ)*(base40) + (65690532889/1000000000000 : ℝ)*(base49) + (29337/200000000000 : ℝ)*(base50) + (2183801793593/1000000000000 : ℝ)*(major_s1_0) + (2183801793593/1000000000000 : ℝ)*(major_s1_1) + (2183801793593/1000000000000 : ℝ)*(major_s1_2) + (9904489/200000000000 : ℝ)*(sp_s1_2) + (6041517/100000000000 : ℝ)*(sp_s1_9) + (2447266371501/1000000000000 : ℝ)*(sp_s1_21) + (2447270091483/1000000000000 : ℝ)*(sp_s1_22) + (611790038467/250000000000 : ℝ)*(sp_s1_23) + (2229253752747/1000000000000 : ℝ)*(sp_s1_27) + (141634246533/100000000000 : ℝ)*(f.failure) + (2447270091483/1000000000000 : ℝ)*(f.sum) + (427985666663239347/2542177580000000000000000000000 : ℝ)*base63 + (4874928878463931/9159900000000000000000000000 : ℝ)*base64 + (31393058249757/83260000000000000000000000 : ℝ)*base66 + (4621623964185299/9159900000000000000000000000 : ℝ)*base68 + (188237909704165361351/751615594500000000000000000000000 : ℝ)*base70 + (466642493794717/8205500000000000000000000000 : ℝ)*base72 + (78614517239299/312225000000000000000000000 : ℝ)*base74 + (3395624324280477/4102750000000000000000000000 : ℝ)*base76 + (3400065858074802801/8539874125000000000000000000000 : ℝ)*base79 + (3569/5000000000000000 : ℝ)*base87 + (3569/5000000000000000 : ℝ)*base89 + (3569/5000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((16411/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16411/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((87423/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(87423/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91599/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(91599/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((65139/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(65139/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((66541/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(66541/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4631/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4631/6250 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306083_s1 p hpa hpb X hX hprev0

#print axioms solution
