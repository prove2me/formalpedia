-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p016_b014
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:10:01.135033+00:00
-- url     : https://prove2.me/submissions/2c2fa5f6-1f1b-4f6e-baa9-ba74782390f2

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
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
theorem collision_support_c316029_s0_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3898844721/10000000000 : ℝ)*x 0 + (3768976503/10000000000 : ℝ)*x 1 + (2419560397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3898844721/10000000000 : ℝ)^39 ≤ (6115064125171/20000000000000 : ℝ)^31 := by
    have hnat : (3898844721 : ℕ)^39*20000000000000^31 ≤ 6115064125171^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3898844721 10000000000 6115064125171 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3768976503/10000000000 : ℝ)^39 ≤ (29299602904139/100000000000000 : ℝ)^31 := by
    have hnat : (3768976503 : ℕ)^39*100000000000000^31 ≤ 29299602904139^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3768976503 10000000000 29299602904139 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2419560397/5000000000 : ℝ)^39 ≤ (40125076454533/100000000000000 : ℝ)^31 := by
    have hnat : (2419560397 : ℕ)^39*100000000000000^31 ≤ 40125076454533^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2419560397 5000000000 40125076454533 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3898844721/10000000000 : ℝ), (3768976503/10000000000 : ℝ), (2419560397/5000000000 : ℝ)] ![(6115064125171/20000000000000 : ℝ), (29299602904139/100000000000000 : ℝ), (40125076454533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3898844721/10000000000 : ℝ)|^39 ≤ (6115064125171/20000000000000 : ℝ)^31
        have hw : |(-3898844721/10000000000 : ℝ)|=(3898844721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3768976503/10000000000 : ℝ)|^39 ≤ (29299602904139/100000000000000 : ℝ)^31
        have hw : |(3768976503/10000000000 : ℝ)|=(3768976503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2419560397/5000000000 : ℝ)|^39 ≤ (40125076454533/100000000000000 : ℝ)^31
        have hw : |(2419560397/5000000000 : ℝ)|=(2419560397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1508093899/2500000000 : ℝ)*x 0 + (-1001514491/10000000000 : ℝ)*x 1 + (2486312417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1508093899/2500000000 : ℝ)^39 ≤ (52946860413823/100000000000000 : ℝ)^31 := by
    have hnat : (1508093899 : ℕ)^39*100000000000000^31 ≤ 52946860413823^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508093899 2500000000 52946860413823 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001514491/10000000000 : ℝ)^39 ≤ (1382618423983/25000000000000 : ℝ)^31 := by
    have hnat : (1001514491 : ℕ)^39*25000000000000^31 ≤ 1382618423983^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001514491 10000000000 1382618423983 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2486312417/5000000000 : ℝ)^39 ≤ (20761332935427/50000000000000 : ℝ)^31 := by
    have hnat : (2486312417 : ℕ)^39*50000000000000^31 ≤ 20761332935427^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486312417 5000000000 20761332935427 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1508093899/2500000000 : ℝ), (-1001514491/10000000000 : ℝ), (2486312417/5000000000 : ℝ)] ![(52946860413823/100000000000000 : ℝ), (1382618423983/25000000000000 : ℝ), (20761332935427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1508093899/2500000000 : ℝ)|^39 ≤ (52946860413823/100000000000000 : ℝ)^31
        have hw : |(1508093899/2500000000 : ℝ)|=(1508093899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1001514491/10000000000 : ℝ)|^39 ≤ (1382618423983/25000000000000 : ℝ)^31
        have hw : |(-1001514491/10000000000 : ℝ)|=(1001514491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2486312417/5000000000 : ℝ)|^39 ≤ (20761332935427/50000000000000 : ℝ)^31
        have hw : |(2486312417/5000000000 : ℝ)|=(2486312417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (237292987/1250000000 : ℝ)*x 0 + (478235419/625000000 : ℝ)*x 1 + (-2356163447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (237292987/1250000000 : ℝ)^39 ≤ (2472743398247/20000000000000 : ℝ)^31 := by
    have hnat : (237292987 : ℕ)^39*20000000000000^31 ≤ 2472743398247^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237292987 1250000000 2472743398247 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478235419/625000000 : ℝ)^39 ≤ (17852734795661/25000000000000 : ℝ)^31 := by
    have hnat : (478235419 : ℕ)^39*25000000000000^31 ≤ 17852734795661^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478235419 625000000 17852734795661 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2356163447/10000000000 : ℝ)^39 ≤ (16225343809943/100000000000000 : ℝ)^31 := by
    have hnat : (2356163447 : ℕ)^39*100000000000000^31 ≤ 16225343809943^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356163447 10000000000 16225343809943 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(237292987/1250000000 : ℝ), (478235419/625000000 : ℝ), (-2356163447/10000000000 : ℝ)] ![(2472743398247/20000000000000 : ℝ), (17852734795661/25000000000000 : ℝ), (16225343809943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(237292987/1250000000 : ℝ)|^39 ≤ (2472743398247/20000000000000 : ℝ)^31
        have hw : |(237292987/1250000000 : ℝ)|=(237292987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(478235419/625000000 : ℝ)|^39 ≤ (17852734795661/25000000000000 : ℝ)^31
        have hw : |(478235419/625000000 : ℝ)|=(478235419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2356163447/10000000000 : ℝ)|^39 ≤ (16225343809943/100000000000000 : ℝ)^31
        have hw : |(-2356163447/10000000000 : ℝ)|=(2356163447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_4 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^39 ≤ (0 : ℝ)^31 := by
    have hnat : (0 : ℕ)^39*1^31 ≤ 0^31*1^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^39 ≤ (1 : ℝ)^31 := by
    have hnat : (1 : ℕ)^39*1^31 ≤ 1^31*1^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^39 ≤ (0 : ℝ)^31 := by
    have hnat : (0 : ℕ)^39*1^31 ≤ 0^31*1^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^39 ≤ (0 : ℝ)^31
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^39 ≤ (1 : ℝ)^31
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^39 ≤ (0 : ℝ)^31
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4219703271/10000000000 : ℝ)*x 0 + (11941333/40000000 : ℝ)*x 1 + (5242126087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4219703271/10000000000 : ℝ)^39 ≤ (16886921125409/50000000000000 : ℝ)^31 := by
    have hnat : (4219703271 : ℕ)^39*50000000000000^31 ≤ 16886921125409^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219703271 10000000000 16886921125409 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11941333/40000000 : ℝ)^39 ≤ (21852800133621/100000000000000 : ℝ)^31 := by
    have hnat : (11941333 : ℕ)^39*100000000000000^31 ≤ 21852800133621^31*40000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11941333 40000000 21852800133621 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242126087/10000000000 : ℝ)^39 ≤ (22186678800569/50000000000000 : ℝ)^31 := by
    have hnat : (5242126087 : ℕ)^39*50000000000000^31 ≤ 22186678800569^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242126087 10000000000 22186678800569 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4219703271/10000000000 : ℝ), (11941333/40000000 : ℝ), (5242126087/10000000000 : ℝ)] ![(16886921125409/50000000000000 : ℝ), (21852800133621/100000000000000 : ℝ), (22186678800569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4219703271/10000000000 : ℝ)|^39 ≤ (16886921125409/50000000000000 : ℝ)^31
        have hw : |(-4219703271/10000000000 : ℝ)|=(4219703271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(11941333/40000000 : ℝ)|^39 ≤ (21852800133621/100000000000000 : ℝ)^31
        have hw : |(11941333/40000000 : ℝ)|=(11941333/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242126087/10000000000 : ℝ)|^39 ≤ (22186678800569/50000000000000 : ℝ)^31
        have hw : |(5242126087/10000000000 : ℝ)|=(5242126087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1106136891/2000000000 : ℝ)*x 0 + (-146225181/5000000000 : ℝ)*x 1 + (2943962137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106136891/2000000000 : ℝ)^39 ≤ (47467814616031/100000000000000 : ℝ)^31 := by
    have hnat : (1106136891 : ℕ)^39*100000000000000^31 ≤ 47467814616031^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106136891 2000000000 47467814616031 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146225181/5000000000 : ℝ)^39 ≤ (146928034867/12500000000000 : ℝ)^31 := by
    have hnat : (146225181 : ℕ)^39*12500000000000^31 ≤ 146928034867^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146225181 5000000000 146928034867 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2943962137/5000000000 : ℝ)^39 ≤ (51356761089663/100000000000000 : ℝ)^31 := by
    have hnat : (2943962137 : ℕ)^39*100000000000000^31 ≤ 51356761089663^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2943962137 5000000000 51356761089663 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1106136891/2000000000 : ℝ), (-146225181/5000000000 : ℝ), (2943962137/5000000000 : ℝ)] ![(47467814616031/100000000000000 : ℝ), (146928034867/12500000000000 : ℝ), (51356761089663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1106136891/2000000000 : ℝ)|^39 ≤ (47467814616031/100000000000000 : ℝ)^31
        have hw : |(1106136891/2000000000 : ℝ)|=(1106136891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-146225181/5000000000 : ℝ)|^39 ≤ (146928034867/12500000000000 : ℝ)^31
        have hw : |(-146225181/5000000000 : ℝ)|=(146225181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2943962137/5000000000 : ℝ)|^39 ≤ (51356761089663/100000000000000 : ℝ)^31
        have hw : |(2943962137/5000000000 : ℝ)|=(2943962137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4042057/50000000 : ℝ)*x 0 + (921499583/1000000000 : ℝ)*x 1 + (-1004287319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4042057/50000000 : ℝ)^39 ≤ (4224070136297/100000000000000 : ℝ)^31 := by
    have hnat : (4042057 : ℕ)^39*100000000000000^31 ≤ 4224070136297^31*50000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4042057 50000000 4224070136297 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921499583/1000000000 : ℝ)^39 ≤ (90226185965403/100000000000000 : ℝ)^31 := by
    have hnat : (921499583 : ℕ)^39*100000000000000^31 ≤ 90226185965403^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921499583 1000000000 90226185965403 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004287319/10000000000 : ℝ)^39 ≤ (221989755359/4000000000000 : ℝ)^31 := by
    have hnat : (1004287319 : ℕ)^39*4000000000000^31 ≤ 221989755359^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004287319 10000000000 221989755359 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4042057/50000000 : ℝ), (921499583/1000000000 : ℝ), (-1004287319/10000000000 : ℝ)] ![(4224070136297/100000000000000 : ℝ), (90226185965403/100000000000000 : ℝ), (221989755359/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4042057/50000000 : ℝ)|^39 ≤ (4224070136297/100000000000000 : ℝ)^31
        have hw : |(4042057/50000000 : ℝ)|=(4042057/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(921499583/1000000000 : ℝ)|^39 ≤ (90226185965403/100000000000000 : ℝ)^31
        have hw : |(921499583/1000000000 : ℝ)|=(921499583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1004287319/10000000000 : ℝ)|^39 ≤ (221989755359/4000000000000 : ℝ)^31
        have hw : |(-1004287319/10000000000 : ℝ)|=(1004287319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_12 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (536333461/1250000000 : ℝ)*x 0 + (3655526789/10000000000 : ℝ)*x 1 + (456781193/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536333461/1250000000 : ℝ)^39 ≤ (34489952055277/100000000000000 : ℝ)^31 := by
    have hnat : (536333461 : ℕ)^39*100000000000000^31 ≤ 34489952055277^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536333461 1250000000 34489952055277 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3655526789/10000000000 : ℝ)^39 ≤ (1409720031673/5000000000000 : ℝ)^31 := by
    have hnat : (3655526789 : ℕ)^39*5000000000000^31 ≤ 1409720031673^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3655526789 10000000000 1409720031673 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456781193/1000000000 : ℝ)^39 ≤ (37315647292157/100000000000000 : ℝ)^31 := by
    have hnat : (456781193 : ℕ)^39*100000000000000^31 ≤ 37315647292157^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456781193 1000000000 37315647292157 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536333461/1250000000 : ℝ), (3655526789/10000000000 : ℝ), (456781193/1000000000 : ℝ)] ![(34489952055277/100000000000000 : ℝ), (1409720031673/5000000000000 : ℝ), (37315647292157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536333461/1250000000 : ℝ)|^39 ≤ (34489952055277/100000000000000 : ℝ)^31
        have hw : |(536333461/1250000000 : ℝ)|=(536333461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3655526789/10000000000 : ℝ)|^39 ≤ (1409720031673/5000000000000 : ℝ)^31
        have hw : |(3655526789/10000000000 : ℝ)|=(3655526789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(456781193/1000000000 : ℝ)|^39 ≤ (37315647292157/100000000000000 : ℝ)^31
        have hw : |(456781193/1000000000 : ℝ)|=(456781193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4367786391/10000000000 : ℝ)*x 0 + (2686744241/10000000000 : ℝ)*x 1 + (133898801/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367786391/10000000000 : ℝ)^39 ≤ (17635818679271/50000000000000 : ℝ)^31 := by
    have hnat : (4367786391 : ℕ)^39*50000000000000^31 ≤ 17635818679271^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367786391 10000000000 17635818679271 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2686744241/10000000000 : ℝ)^39 ≤ (9569734723597/50000000000000 : ℝ)^31 := by
    have hnat : (2686744241 : ℕ)^39*50000000000000^31 ≤ 9569734723597^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686744241 10000000000 9569734723597 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133898801/250000000 : ℝ)^39 ≤ (9117778634807/20000000000000 : ℝ)^31 := by
    have hnat : (133898801 : ℕ)^39*20000000000000^31 ≤ 9117778634807^31*250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133898801 250000000 9117778634807 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4367786391/10000000000 : ℝ), (2686744241/10000000000 : ℝ), (133898801/250000000 : ℝ)] ![(17635818679271/50000000000000 : ℝ), (9569734723597/50000000000000 : ℝ), (9117778634807/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4367786391/10000000000 : ℝ)|^39 ≤ (17635818679271/50000000000000 : ℝ)^31
        have hw : |(-4367786391/10000000000 : ℝ)|=(4367786391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2686744241/10000000000 : ℝ)|^39 ≤ (9569734723597/50000000000000 : ℝ)^31
        have hw : |(2686744241/10000000000 : ℝ)|=(2686744241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(133898801/250000000 : ℝ)|^39 ≤ (9117778634807/20000000000000 : ℝ)^31
        have hw : |(133898801/250000000 : ℝ)|=(133898801/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (861937117/1250000000 : ℝ)*x 0 + (-1286455377/10000000000 : ℝ)*x 1 + (119294467/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861937117/1250000000 : ℝ)^39 ≤ (62647691410347/100000000000000 : ℝ)^31 := by
    have hnat : (861937117 : ℕ)^39*100000000000000^31 ≤ 62647691410347^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861937117 1250000000 62647691410347 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1286455377/10000000000 : ℝ)^39 ≤ (94726419187/1250000000000 : ℝ)^31 := by
    have hnat : (1286455377 : ℕ)^39*1250000000000^31 ≤ 94726419187^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286455377 10000000000 94726419187 1250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119294467/312500000 : ℝ)^39 ≤ (14887097520523/50000000000000 : ℝ)^31 := by
    have hnat : (119294467 : ℕ)^39*50000000000000^31 ≤ 14887097520523^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119294467 312500000 14887097520523 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861937117/1250000000 : ℝ), (-1286455377/10000000000 : ℝ), (119294467/312500000 : ℝ)] ![(62647691410347/100000000000000 : ℝ), (94726419187/1250000000000 : ℝ), (14887097520523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861937117/1250000000 : ℝ)|^39 ≤ (62647691410347/100000000000000 : ℝ)^31
        have hw : |(861937117/1250000000 : ℝ)|=(861937117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1286455377/10000000000 : ℝ)|^39 ≤ (94726419187/1250000000000 : ℝ)^31
        have hw : |(-1286455377/10000000000 : ℝ)|=(1286455377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119294467/312500000 : ℝ)|^39 ≤ (14887097520523/50000000000000 : ℝ)^31
        have hw : |(119294467/312500000 : ℝ)|=(119294467/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1502543179/10000000000 : ℝ)*x 0 + (7865413611/10000000000 : ℝ)*x 1 + (-1214495299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1502543179/10000000000 : ℝ)^39 ≤ (1151609456307/12500000000000 : ℝ)^31 := by
    have hnat : (1502543179 : ℕ)^39*12500000000000^31 ≤ 1151609456307^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502543179 10000000000 1151609456307 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7865413611/10000000000 : ℝ)^39 ≤ (73928348006897/100000000000000 : ℝ)^31 := by
    have hnat : (7865413611 : ℕ)^39*100000000000000^31 ≤ 73928348006897^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7865413611 10000000000 73928348006897 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1214495299/5000000000 : ℝ)^39 ≤ (3371755267071/20000000000000 : ℝ)^31 := by
    have hnat : (1214495299 : ℕ)^39*20000000000000^31 ≤ 3371755267071^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214495299 5000000000 3371755267071 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1502543179/10000000000 : ℝ), (7865413611/10000000000 : ℝ), (-1214495299/5000000000 : ℝ)] ![(1151609456307/12500000000000 : ℝ), (73928348006897/100000000000000 : ℝ), (3371755267071/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1502543179/10000000000 : ℝ)|^39 ≤ (1151609456307/12500000000000 : ℝ)^31
        have hw : |(1502543179/10000000000 : ℝ)|=(1502543179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7865413611/10000000000 : ℝ)|^39 ≤ (73928348006897/100000000000000 : ℝ)^31
        have hw : |(7865413611/10000000000 : ℝ)|=(7865413611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1214495299/5000000000 : ℝ)|^39 ≤ (3371755267071/20000000000000 : ℝ)^31
        have hw : |(-1214495299/5000000000 : ℝ)|=(1214495299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_19 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2960583743/10000000000 : ℝ)*x 0 + (17475461/50000000 : ℝ)*x 1 + (5921757053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2960583743/10000000000 : ℝ)^39 ≤ (10812561881427/50000000000000 : ℝ)^31 := by
    have hnat : (2960583743 : ℕ)^39*50000000000000^31 ≤ 10812561881427^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2960583743 10000000000 10812561881427 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17475461/50000000 : ℝ)^39 ≤ (13323291049083/50000000000000 : ℝ)^31 := by
    have hnat : (17475461 : ℕ)^39*50000000000000^31 ≤ 13323291049083^31*50000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17475461 50000000 13323291049083 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5921757053/10000000000 : ℝ)^39 ≤ (51728294113147/100000000000000 : ℝ)^31 := by
    have hnat : (5921757053 : ℕ)^39*100000000000000^31 ≤ 51728294113147^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5921757053 10000000000 51728294113147 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2960583743/10000000000 : ℝ), (17475461/50000000 : ℝ), (5921757053/10000000000 : ℝ)] ![(10812561881427/50000000000000 : ℝ), (13323291049083/50000000000000 : ℝ), (51728294113147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2960583743/10000000000 : ℝ)|^39 ≤ (10812561881427/50000000000000 : ℝ)^31
        have hw : |(2960583743/10000000000 : ℝ)|=(2960583743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17475461/50000000 : ℝ)|^39 ≤ (13323291049083/50000000000000 : ℝ)^31
        have hw : |(17475461/50000000 : ℝ)|=(17475461/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5921757053/10000000000 : ℝ)|^39 ≤ (51728294113147/100000000000000 : ℝ)^31
        have hw : |(5921757053/10000000000 : ℝ)|=(5921757053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1515459529/5000000000 : ℝ)*x 0 + (464649651/1250000000 : ℝ)*x 1 + (5665908223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1515459529/5000000000 : ℝ)^39 ≤ (445468568811/2000000000000 : ℝ)^31 := by
    have hnat : (1515459529 : ℕ)^39*2000000000000^31 ≤ 445468568811^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515459529 5000000000 445468568811 2000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464649651/1250000000 : ℝ)^39 ≤ (287940994063/1000000000000 : ℝ)^31 := by
    have hnat : (464649651 : ℕ)^39*1000000000000^31 ≤ 287940994063^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464649651 1250000000 287940994063 1000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5665908223/10000000000 : ℝ)^39 ≤ (12233118036361/25000000000000 : ℝ)^31 := by
    have hnat : (5665908223 : ℕ)^39*25000000000000^31 ≤ 12233118036361^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665908223 10000000000 12233118036361 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1515459529/5000000000 : ℝ), (464649651/1250000000 : ℝ), (5665908223/10000000000 : ℝ)] ![(445468568811/2000000000000 : ℝ), (287940994063/1000000000000 : ℝ), (12233118036361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1515459529/5000000000 : ℝ)|^39 ≤ (445468568811/2000000000000 : ℝ)^31
        have hw : |(-1515459529/5000000000 : ℝ)|=(1515459529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(464649651/1250000000 : ℝ)|^39 ≤ (287940994063/1000000000000 : ℝ)^31
        have hw : |(464649651/1250000000 : ℝ)|=(464649651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5665908223/10000000000 : ℝ)|^39 ≤ (12233118036361/25000000000000 : ℝ)^31
        have hw : |(5665908223/10000000000 : ℝ)|=(5665908223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3760206653/5000000000 : ℝ)*x 0 + (-32761109/1000000000 : ℝ)*x 1 + (464365659/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3760206653/5000000000 : ℝ)^39 ≤ (68234518153/97656250000 : ℝ)^31 := by
    have hnat : (3760206653 : ℕ)^39*97656250000^31 ≤ 68234518153^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3760206653 5000000000 68234518153 97656250000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32761109/1000000000 : ℝ)^39 ≤ (271178543911/20000000000000 : ℝ)^31 := by
    have hnat : (32761109 : ℕ)^39*20000000000000^31 ≤ 271178543911^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32761109 1000000000 271178543911 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464365659/1250000000 : ℝ)^39 ≤ (28771960679189/100000000000000 : ℝ)^31 := by
    have hnat : (464365659 : ℕ)^39*100000000000000^31 ≤ 28771960679189^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464365659 1250000000 28771960679189 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3760206653/5000000000 : ℝ), (-32761109/1000000000 : ℝ), (464365659/1250000000 : ℝ)] ![(68234518153/97656250000 : ℝ), (271178543911/20000000000000 : ℝ), (28771960679189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3760206653/5000000000 : ℝ)|^39 ≤ (68234518153/97656250000 : ℝ)^31
        have hw : |(3760206653/5000000000 : ℝ)|=(3760206653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32761109/1000000000 : ℝ)|^39 ≤ (271178543911/20000000000000 : ℝ)^31
        have hw : |(-32761109/1000000000 : ℝ)|=(32761109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(464365659/1250000000 : ℝ)|^39 ≤ (28771960679189/100000000000000 : ℝ)^31
        have hw : |(464365659/1250000000 : ℝ)|=(464365659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (817633981/10000000000 : ℝ)*x 0 + (889497423/1000000000 : ℝ)*x 1 + (-1528460183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (817633981/10000000000 : ℝ)^39 ≤ (214239222691/5000000000000 : ℝ)^31 := by
    have hnat : (817633981 : ℕ)^39*5000000000000^31 ≤ 214239222691^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817633981 10000000000 214239222691 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (889497423/1000000000 : ℝ)^39 ≤ (21575494235549/25000000000000 : ℝ)^31 := by
    have hnat : (889497423 : ℕ)^39*25000000000000^31 ≤ 21575494235549^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889497423 1000000000 21575494235549 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1528460183/10000000000 : ℝ)^39 ≤ (9413238585699/100000000000000 : ℝ)^31 := by
    have hnat : (1528460183 : ℕ)^39*100000000000000^31 ≤ 9413238585699^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528460183 10000000000 9413238585699 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(817633981/10000000000 : ℝ), (889497423/1000000000 : ℝ), (-1528460183/10000000000 : ℝ)] ![(214239222691/5000000000000 : ℝ), (21575494235549/25000000000000 : ℝ), (9413238585699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(817633981/10000000000 : ℝ)|^39 ≤ (214239222691/5000000000000 : ℝ)^31
        have hw : |(817633981/10000000000 : ℝ)|=(817633981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(889497423/1000000000 : ℝ)|^39 ≤ (21575494235549/25000000000000 : ℝ)^31
        have hw : |(889497423/1000000000 : ℝ)|=(889497423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1528460183/10000000000 : ℝ)|^39 ≤ (9413238585699/100000000000000 : ℝ)^31
        have hw : |(-1528460183/10000000000 : ℝ)|=(1528460183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s0_25 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (814473741/1250000000 : ℝ)*x 0 + (2517841907/10000000000 : ℝ)*x 1 + (64373251/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (814473741/1250000000 : ℝ)^39 ≤ (29169472896091/50000000000000 : ℝ)^31 := by
    have hnat : (814473741 : ℕ)^39*50000000000000^31 ≤ 29169472896091^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814473741 1250000000 29169472896091 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2517841907/10000000000 : ℝ)^39 ≤ (35276472589/200000000000 : ℝ)^31 := by
    have hnat : (2517841907 : ℕ)^39*200000000000^31 ≤ 35276472589^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517841907 10000000000 35276472589 200000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64373251/200000000 : ℝ)^39 ≤ (24022817906289/100000000000000 : ℝ)^31 := by
    have hnat : (64373251 : ℕ)^39*100000000000000^31 ≤ 24022817906289^31*200000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64373251 200000000 24022817906289 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(814473741/1250000000 : ℝ), (2517841907/10000000000 : ℝ), (64373251/200000000 : ℝ)] ![(29169472896091/50000000000000 : ℝ), (35276472589/200000000000 : ℝ), (24022817906289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(814473741/1250000000 : ℝ)|^39 ≤ (29169472896091/50000000000000 : ℝ)^31
        have hw : |(814473741/1250000000 : ℝ)|=(814473741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2517841907/10000000000 : ℝ)|^39 ≤ (35276472589/200000000000 : ℝ)^31
        have hw : |(2517841907/10000000000 : ℝ)|=(2517841907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64373251/200000000 : ℝ)|^39 ≤ (24022817906289/100000000000000 : ℝ)^31
        have hw : |(64373251/200000000 : ℝ)|=(64373251/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2003739797/5000000000 : ℝ)*x 0 + (4123679557/10000000000 : ℝ)*x 1 + (1098527273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003739797/5000000000 : ℝ)^39 ≤ (15825465854259/50000000000000 : ℝ)^31 := by
    have hnat : (2003739797 : ℕ)^39*50000000000000^31 ≤ 15825465854259^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003739797 5000000000 15825465854259 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4123679557/10000000000 : ℝ)^39 ≤ (32809800989377/100000000000000 : ℝ)^31 := by
    have hnat : (4123679557 : ℕ)^39*100000000000000^31 ≤ 32809800989377^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123679557 10000000000 32809800989377 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098527273/2500000000 : ℝ)^39 ≤ (1110602102697/3125000000000 : ℝ)^31 := by
    have hnat : (1098527273 : ℕ)^39*3125000000000^31 ≤ 1110602102697^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098527273 2500000000 1110602102697 3125000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2003739797/5000000000 : ℝ), (4123679557/10000000000 : ℝ), (1098527273/2500000000 : ℝ)] ![(15825465854259/50000000000000 : ℝ), (32809800989377/100000000000000 : ℝ), (1110602102697/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2003739797/5000000000 : ℝ)|^39 ≤ (15825465854259/50000000000000 : ℝ)^31
        have hw : |(-2003739797/5000000000 : ℝ)|=(2003739797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4123679557/10000000000 : ℝ)|^39 ≤ (32809800989377/100000000000000 : ℝ)^31
        have hw : |(4123679557/10000000000 : ℝ)|=(4123679557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098527273/2500000000 : ℝ)|^39 ≤ (1110602102697/3125000000000 : ℝ)^31
        have hw : |(1098527273/2500000000 : ℝ)|=(1098527273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2648903411/5000000000 : ℝ)*x 0 + (-2255445691/10000000000 : ℝ)*x 1 + (4795947817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648903411/5000000000 : ℝ)^39 ≤ (44967124473269/100000000000000 : ℝ)^31 := by
    have hnat : (2648903411 : ℕ)^39*100000000000000^31 ≤ 44967124473269^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648903411 5000000000 44967124473269 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255445691/10000000000 : ℝ)^39 ≤ (15357644127391/100000000000000 : ℝ)^31 := by
    have hnat : (2255445691 : ℕ)^39*100000000000000^31 ≤ 15357644127391^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255445691 10000000000 15357644127391 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4795947817/10000000000 : ℝ)^39 ≤ (39675231378519/100000000000000 : ℝ)^31 := by
    have hnat : (4795947817 : ℕ)^39*100000000000000^31 ≤ 39675231378519^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795947817 10000000000 39675231378519 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648903411/5000000000 : ℝ), (-2255445691/10000000000 : ℝ), (4795947817/10000000000 : ℝ)] ![(44967124473269/100000000000000 : ℝ), (15357644127391/100000000000000 : ℝ), (39675231378519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648903411/5000000000 : ℝ)|^39 ≤ (44967124473269/100000000000000 : ℝ)^31
        have hw : |(2648903411/5000000000 : ℝ)|=(2648903411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2255445691/10000000000 : ℝ)|^39 ≤ (15357644127391/100000000000000 : ℝ)^31
        have hw : |(-2255445691/10000000000 : ℝ)|=(2255445691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4795947817/10000000000 : ℝ)|^39 ≤ (39675231378519/100000000000000 : ℝ)^31
        have hw : |(4795947817/10000000000 : ℝ)|=(4795947817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1479367919/5000000000 : ℝ)*x 0 + (1227840369/2000000000 : ℝ)*x 1 + (-3244185713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1479367919/5000000000 : ℝ)^39 ≤ (4321628821887/20000000000000 : ℝ)^31 := by
    have hnat : (1479367919 : ℕ)^39*20000000000000^31 ≤ 4321628821887^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479367919 5000000000 4321628821887 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1227840369/2000000000 : ℝ)^39 ≤ (5412913856157/10000000000000 : ℝ)^31 := by
    have hnat : (1227840369 : ℕ)^39*10000000000000^31 ≤ 5412913856157^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227840369 2000000000 5412913856157 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3244185713/10000000000 : ℝ)^39 ≤ (1516419832333/6250000000000 : ℝ)^31 := by
    have hnat : (3244185713 : ℕ)^39*6250000000000^31 ≤ 1516419832333^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3244185713 10000000000 1516419832333 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1479367919/5000000000 : ℝ), (1227840369/2000000000 : ℝ), (-3244185713/10000000000 : ℝ)] ![(4321628821887/20000000000000 : ℝ), (5412913856157/10000000000000 : ℝ), (1516419832333/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1479367919/5000000000 : ℝ)|^39 ≤ (4321628821887/20000000000000 : ℝ)^31
        have hw : |(1479367919/5000000000 : ℝ)|=(1479367919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1227840369/2000000000 : ℝ)|^39 ≤ (5412913856157/10000000000000 : ℝ)^31
        have hw : |(1227840369/2000000000 : ℝ)|=(1227840369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3244185713/10000000000 : ℝ)|^39 ≤ (1516419832333/6250000000000 : ℝ)^31
        have hw : |(-3244185713/10000000000 : ℝ)|=(3244185713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316029_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (113262269/250000000 : ℝ)*x 0 + (31114557/80000000 : ℝ)*x 1 + (2050659641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113262269/250000000 : ℝ)^39 ≤ (18466242880243/50000000000000 : ℝ)^31 := by
    have hnat : (113262269 : ℕ)^39*50000000000000^31 ≤ 18466242880243^31*250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113262269 250000000 18466242880243 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31114557/80000000 : ℝ)^39 ≤ (30481376344773/100000000000000 : ℝ)^31 := by
    have hnat : (31114557 : ℕ)^39*100000000000000^31 ≤ 30481376344773^31*80000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31114557 80000000 30481376344773 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050659641/5000000000 : ℝ)^39 ≤ (8146534469247/25000000000000 : ℝ)^31 := by
    have hnat : (2050659641 : ℕ)^39*25000000000000^31 ≤ 8146534469247^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050659641 5000000000 8146534469247 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(113262269/250000000 : ℝ), (31114557/80000000 : ℝ), (2050659641/5000000000 : ℝ)] ![(18466242880243/50000000000000 : ℝ), (30481376344773/100000000000000 : ℝ), (8146534469247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(113262269/250000000 : ℝ)|^39 ≤ (18466242880243/50000000000000 : ℝ)^31
        have hw : |(113262269/250000000 : ℝ)|=(113262269/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31114557/80000000 : ℝ)|^39 ≤ (30481376344773/100000000000000 : ℝ)^31
        have hw : |(31114557/80000000 : ℝ)|=(31114557/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2050659641/5000000000 : ℝ)|^39 ≤ (8146534469247/25000000000000 : ℝ)^31
        have hw : |(2050659641/5000000000 : ℝ)|=(2050659641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316029 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3898844721/10000000000 : ℝ)*X 0 0+(3768976503/10000000000 : ℝ)*X 0 1+(2419560397/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1508093899/2500000000 : ℝ)*X 1 0+(-1001514491/10000000000 : ℝ)*X 1 1+(2486312417/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((237292987/1250000000 : ℝ)*X 2 0+(478235419/625000000 : ℝ)*X 2 1+(-2356163447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-4219703271/10000000000 : ℝ)*X 0 0+(11941333/40000000 : ℝ)*X 0 1+(5242126087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1106136891/2000000000 : ℝ)*X 1 0+(-146225181/5000000000 : ℝ)*X 1 1+(2943962137/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4042057/50000000 : ℝ)*X 2 0+(921499583/1000000000 : ℝ)*X 2 1+(-1004287319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((536333461/1250000000 : ℝ)*X 0 0+(3655526789/10000000000 : ℝ)*X 0 1+(456781193/1000000000 : ℝ)*X 0 2+(536333461/1250000000 : ℝ)*X 1 0+(3655526789/10000000000 : ℝ)*X 1 1+(456781193/1000000000 : ℝ)*X 1 2+(536333461/1250000000 : ℝ)*X 2 0+(3655526789/10000000000 : ℝ)*X 2 1+(456781193/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-4367786391/10000000000 : ℝ)*X 0 0+(2686744241/10000000000 : ℝ)*X 0 1+(133898801/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((861937117/1250000000 : ℝ)*X 1 0+(-1286455377/10000000000 : ℝ)*X 1 1+(119294467/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1502543179/10000000000 : ℝ)*X 2 0+(7865413611/10000000000 : ℝ)*X 2 1+(-1214495299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((2960583743/10000000000 : ℝ)*X 0 0+(17475461/50000000 : ℝ)*X 0 1+(5921757053/10000000000 : ℝ)*X 0 2+(2960583743/10000000000 : ℝ)*X 1 0+(17475461/50000000 : ℝ)*X 1 1+(5921757053/10000000000 : ℝ)*X 1 2+(2960583743/10000000000 : ℝ)*X 2 0+(17475461/50000000 : ℝ)*X 2 1+(5921757053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1515459529/5000000000 : ℝ)*X 0 0+(464649651/1250000000 : ℝ)*X 0 1+(5665908223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((3760206653/5000000000 : ℝ)*X 1 0+(-32761109/1000000000 : ℝ)*X 1 1+(464365659/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((817633981/10000000000 : ℝ)*X 2 0+(889497423/1000000000 : ℝ)*X 2 1+(-1528460183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((814473741/1250000000 : ℝ)*X 0 0+(2517841907/10000000000 : ℝ)*X 0 1+(64373251/200000000 : ℝ)*X 0 2+(814473741/1250000000 : ℝ)*X 1 0+(2517841907/10000000000 : ℝ)*X 1 1+(64373251/200000000 : ℝ)*X 1 2+(814473741/1250000000 : ℝ)*X 2 0+(2517841907/10000000000 : ℝ)*X 2 1+(64373251/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((32487/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32487/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (73477791081863647424709/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (268838274687/500000000000 : ℝ)*(base50) + (703864232997/1000000000000 : ℝ)*(base59) + (2686393730177/1000000000000 : ℝ)*(major_s0_0) + (5485076546259/1000000000000 : ℝ)*(major_s0_1) + (2686393730177/1000000000000 : ℝ)*(major_s0_2) + (12935157/100000000000 : ℝ)*(sp_s0_0) + (11957663/500000000000 : ℝ)*(sp_s0_1) + (1399341408041/500000000000 : ℝ)*(sp_s0_4) + (3857117163627/1000000000000 : ℝ)*(sp_s0_7) + (385722259987/100000000000 : ℝ)*(sp_s0_8) + (385708942533/100000000000 : ℝ)*(sp_s0_9) + (757749220559/500000000000 : ℝ)*(sp_s0_12) + (37605513/1000000000000 : ℝ)*(sp_s0_19) + (78544933/500000000000 : ℝ)*(sp_s0_22) + (1515536046631/1000000000000 : ℝ)*(f.failure) + (3857246515197/1000000000000 : ℝ)*(f.sum) + (2997971129892841/5000000000000000000000000000 : ℝ)*base63 + (33788180227047/5000000000000000000000000000 : ℝ)*base64 + (893820691800549/5000000000000000000000000000 : ℝ)*base67 + (4759911563684223/10000000000000000000000000000 : ℝ)*base69 + (565810158230129/10000000000000000000000000000 : ℝ)*base71 + (2000444502727047/5000000000000000000000000000 : ℝ)*base73 + (5126270774101459/10000000000000000000000000000 : ℝ)*base75 + (6532951270684223/10000000000000000000000000000 : ℝ)*base77 + (336491432381899/1250000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (28833/100000000000000000 : ℝ)*base86 + (28833/100000000000000000 : ℝ)*base88 + (28833/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11191/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(11191/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43850504996866421068581/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (571881/40000000000 : ℝ)*(base3) + (19204302501/40000000000 : ℝ)*(base40) + (9886193/1000000000000 : ℝ)*(base50) + (570387640209/1000000000000 : ℝ)*(base59) + (2173335823187/1000000000000 : ℝ)*(major_s0_0) + (2173335823187/1000000000000 : ℝ)*(major_s0_1) + (2173335823187/1000000000000 : ℝ)*(major_s0_2) + (11675613/200000000000 : ℝ)*(sp_s0_1) + (22399587/500000000000 : ℝ)*(sp_s0_2) + (3120575636023/1000000000000 : ℝ)*(sp_s0_13) + (3120508459147/1000000000000 : ℝ)*(sp_s0_14) + (3120530836849/1000000000000 : ℝ)*(sp_s0_15) + (245215757991/200000000000 : ℝ)*(sp_s0_19) + (5773959/250000000000 : ℝ)*(sp_s0_21) + (61304654349/50000000000 : ℝ)*(f.failure) + (3120575636023/1000000000000 : ℝ)*(f.sum) + (113984643/2500000000000000000000 : ℝ)*base62 + (2853620570113157/5000000000000000000000000000 : ℝ)*base64 + (1285071468886843/5000000000000000000000000000 : ℝ)*base66 + (5670151544536787/10000000000000000000000000000 : ℝ)*base68 + (2846883854763101/10000000000000000000000000000 : ℝ)*base70 + (2672254193886843/5000000000000000000000000000 : ℝ)*base72 + (2469765608463213/10000000000000000000000000000 : ℝ)*base74 + (3034186066536787/10000000000000000000000000000 : ℝ)*base76 + (129317735136843/2500000000000000000000000000 : ℝ)*base78 + (5693/5000000000000000 : ℝ)*base87 + (5693/5000000000000000 : ℝ)*base89 + (5693/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21703/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21703/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6002456952824230933563/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (902929811443/1000000000000 : ℝ)*(base40) + (451054185841/1000000000000 : ℝ)*(base50) + (761679708637/1000000000000 : ℝ)*(base59) + (215297807893/62500000000 : ℝ)*(major_s0_0) + (2105265401801/250000000000 : ℝ)*(major_s0_1) + (215297807893/62500000000 : ℝ)*(major_s0_2) + (4136087/125000000000 : ℝ)*(sp_s0_0) + (1244074170229/250000000000 : ℝ)*(sp_s0_4) + (22782269/1000000000000 : ℝ)*(sp_s0_14) + (556703/200000000000 : ℝ)*(sp_s0_15) + (494612202349/100000000000 : ℝ)*(sp_s0_20) + (4946132329917/1000000000000 : ℝ)*(sp_s0_21) + (4946152328671/1000000000000 : ℝ)*(sp_s0_22) + (121460821233/62500000000 : ℝ)*(sp_s0_25) + (121460821233/62500000000 : ℝ)*(f.failure) + (2473077556093/500000000000 : ℝ)*(f.sum) + (601903935741429/2500000000000000000000000000 : ℝ)*base63 + (249029666417277/312500000000000000000000000 : ℝ)*base65 + (1072994154056111/1250000000000000000000000000 : ℝ)*base67 + (429730901656707/625000000000000000000000000 : ℝ)*base69 + (239851417053761/625000000000000000000000000 : ℝ)*base71 + (153000456582723/312500000000000000000000000 : ℝ)*base73 + (1790862168614601/2500000000000000000000000000 : ℝ)*base75 + (491281569094207/625000000000000000000000000 : ℝ)*base77 + (197499782512003/1250000000000000000000000000 : ℝ)*base79 + (2119/6250000000000000 : ℝ)*base86 + (2119/6250000000000000 : ℝ)*base88 + (2119/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (32487/100000 : ℝ) ^ (19/4 : ℝ) ≤ (239657290169071407/50000000000000000000 : ℝ) := by
    have hpowers : (32487/100000 : ℝ)^19 ≤ (239657290169071407/50000000000000000000 : ℝ)^4 := by
      have hnat : (32487 : ℕ)^19*50000000000000000000^4 ≤ 239657290169071407^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32487 100000 239657290169071407 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32487/100000 : ℝ)) (X := (239657290169071407/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50239657290169071407/50000000000000000000 : ℝ) ≤ (10010071795502557/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (50239657290169071407/50000000000000000000 : ℝ)^4 ≤ (10010071795502557/10000000000000000 : ℝ)^19 := by
      have hnat : (50239657290169071407 : ℕ)^4*10000000000000000^19 ≤ 10010071795502557^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50239657290169071407 50000000000000000000 10010071795502557 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010071795502557/10000000000000000 : ℝ)) (X := (50239657290169071407/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25239657290169071407/25000000000000000000 : ℝ) ≤ (2004021146328393/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (25239657290169071407/25000000000000000000 : ℝ)^4 ≤ (2004021146328393/2000000000000000 : ℝ)^19 := by
      have hnat : (25239657290169071407 : ℕ)^4*2000000000000000^19 ≤ 2004021146328393^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25239657290169071407 25000000000000000000 2004021146328393 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004021146328393/2000000000000000 : ℝ)) (X := (25239657290169071407/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3357265167519/1082900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(627121008713/203043750000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (32487/100000 : ℝ)) (alpha := (3357265167519/1082900000000000 : ℝ)) (beta := (627121008713/203043750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (32487/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3357265167519/1082900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(627121008713/203043750000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (11191/100000 : ℝ) ^ (19/4 : ℝ) ≤ (606956057968743/20000000000000000000 : ℝ) := by
    have hpowers : (11191/100000 : ℝ)^19 ≤ (606956057968743/20000000000000000000 : ℝ)^4 := by
      have hnat : (11191 : ℕ)^19*20000000000000000000^4 ≤ 606956057968743^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11191 100000 606956057968743 20000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11191/100000 : ℝ)) (X := (606956057968743/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20000606956057968743/20000000000000000000 : ℝ) ≤ (2000012777869203/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (20000606956057968743/20000000000000000000 : ℝ)^4 ≤ (2000012777869203/2000000000000000 : ℝ)^19 := by
      have hnat : (20000606956057968743 : ℕ)^4*2000000000000000^19 ≤ 2000012777869203^19*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20000606956057968743 20000000000000000000 2000012777869203 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000012777869203/2000000000000000 : ℝ)) (X := (20000606956057968743/20000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10000606956057968743/10000000000000000000 : ℝ) ≤ (5000063888580691/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (10000606956057968743/10000000000000000000 : ℝ)^4 ≤ (5000063888580691/5000000000000000 : ℝ)^19 := by
      have hnat : (10000606956057968743 : ℕ)^4*5000000000000000^19 ≤ 5000063888580691^19*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000606956057968743 10000000000000000000 5000063888580691 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000063888580691/5000000000000000 : ℝ)) (X := (10000606956057968743/10000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(12777869203/223820000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(63887815367/1119100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (11191/100000 : ℝ)) (alpha := (12777869203/223820000000000 : ℝ)) (beta := (63887815367/1119100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (11191/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(12777869203/223820000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(63887815367/1119100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (21703/50000 : ℝ) ^ (19/4 : ℝ) ≤ (1898284881286327681/100000000000000000000 : ℝ) := by
    have hpowers : (21703/50000 : ℝ)^19 ≤ (1898284881286327681/100000000000000000000 : ℝ)^4 := by
      have hnat : (21703 : ℕ)^19*100000000000000000000^4 ≤ 1898284881286327681^4*50000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21703 50000 1898284881286327681 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21703/50000 : ℝ)) (X := (1898284881286327681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101898284881286327681/100000000000000000000 : ℝ) ≤ (627479236259939/625000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (101898284881286327681/100000000000000000000 : ℝ)^4 ≤ (627479236259939/625000000000000 : ℝ)^19 := by
      have hnat : (101898284881286327681 : ℕ)^4*625000000000000^19 ≤ 627479236259939^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101898284881286327681 100000000000000000000 627479236259939 625000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (627479236259939/625000000000000 : ℝ)) (X := (101898284881286327681/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51898284881286327681/50000000000000000000 : ℝ) ≤ (1007875637822717/1000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (51898284881286327681/50000000000000000000 : ℝ)^4 ≤ (1007875637822717/1000000000000000 : ℝ)^19 := by
      have hnat : (51898284881286327681 : ℕ)^4*1000000000000000^19 ≤ 1007875637822717^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51898284881286327681 50000000000000000000 1007875637822717 1000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1007875637822717/1000000000000000 : ℝ)) (X := (51898284881286327681/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(2479236259939/271287500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1776754457643/197300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (21703/50000 : ℝ)) (alpha := (2479236259939/271287500000000 : ℝ)) (beta := (1776754457643/197300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (21703/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(2479236259939/271287500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1776754457643/197300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2003739797/5000000000 : ℝ)*X 0 0+(4123679557/10000000000 : ℝ)*X 0 1+(1098527273/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2648903411/5000000000 : ℝ)*X 1 0+(-2255445691/10000000000 : ℝ)*X 1 1+(4795947817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1479367919/5000000000 : ℝ)*X 2 0+(1227840369/2000000000 : ℝ)*X 2 1+(-3244185713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((113262269/250000000 : ℝ)*X 0 0+(31114557/80000000 : ℝ)*X 0 1+(2050659641/5000000000 : ℝ)*X 0 2+(113262269/250000000 : ℝ)*X 1 0+(31114557/80000000 : ℝ)*X 1 1+(2050659641/5000000000 : ℝ)*X 1 2+(113262269/250000000 : ℝ)*X 2 0+(31114557/80000000 : ℝ)*X 2 1+(2050659641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316029_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-381771/50000 : ℝ) < ((-177257/100000 : ℝ)*P 0+(-177257/100000 : ℝ)*P 1+(-177257/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-381771/50000 : ℝ) < (-52352087762921594277589596242055479/6921391627150000000000000000000000 : ℝ) := by norm_num
    linear_combination (89/250000000000 : ℝ)*(base8) + (6263/1000000000000 : ℝ)*(base11) + (158724980457/1000000000000 : ℝ)*(base40) + (318776787631/1000000000000 : ℝ)*(base49) + (573442588349/1000000000000 : ℝ)*(base50) + (6559690969/20000000000 : ℝ)*(base59) + (177257/100000 : ℝ)*(major_s1_0) + (1772570002627/1000000000000 : ℝ)*(major_s1_1) + (177257/100000 : ℝ)*(major_s1_2) + (2521269821409/1000000000000 : ℝ)*(sp_s1_0) + (2521269825913/1000000000000 : ℝ)*(sp_s1_1) + (630317457007/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1260634912701/500000000000 : ℝ)*(f.sum) + (235978596765960633/255661340000000000000000000000 : ℝ)*base62 + (15210301740951/19730000000000000000000000 : ℝ)*base65 + (25566900305809/58900000000000000000000000 : ℝ)*base66 + (55451092670240829/108515000000000000000000000 : ℝ)*base68 + (218844784921669811/213656170000000000000000000000 : ℝ)*base71 + (208253065467527/324870000000000000000000000 : ℝ)*base72 + (3549153430291/11780000000000000000000000 : ℝ)*base74 + (5995521901693/5414500000000000000000000 : ℝ)*base77 + (1994038996327526423/1913484300000000000000000000000 : ℝ)*base78 + (1313/500000000000 : ℝ)*base81 + (511/1000000000000 : ℝ)*base83 + (1313/500000000000 : ℝ)*base85 + (2627/1000000000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p016_b014 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 29 ≤ c.val) (hhi : c.val < 30)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=29 := by omega
  rcases hc with rfl
  · exact collision_c316029 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 29 ≤ c.val) (hhi : c.val < 30)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p016_b014 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
