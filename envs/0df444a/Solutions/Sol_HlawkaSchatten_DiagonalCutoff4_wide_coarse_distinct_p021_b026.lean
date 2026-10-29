-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p021_b026
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:43:43.560435+00:00
-- url     : https://prove2.me/submissions/bfd10446-a11c-4bdc-9eef-e8cd1f4b2c30

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
theorem collision_support_c321047_s0_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-144822559/5000000000 : ℝ)*x 0 + (-306946691/500000000 : ℝ)*x 1 + (1291446039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (144822559/5000000000 : ℝ)^83 ≤ (248645542057/20000000000000 : ℝ)^67 := by
    have hnat : (144822559 : ℕ)^83*20000000000000^67 ≤ 248645542057^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144822559 5000000000 248645542057 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306946691/500000000 : ℝ)^83 ≤ (10927436184693/20000000000000 : ℝ)^67 := by
    have hnat : (306946691 : ℕ)^83*20000000000000^67 ≤ 10927436184693^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306946691 500000000 10927436184693 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291446039/2500000000 : ℝ)^83 ≤ (44119591350243/100000000000000 : ℝ)^67 := by
    have hnat : (1291446039 : ℕ)^83*100000000000000^67 ≤ 44119591350243^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291446039 2500000000 44119591350243 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-144822559/5000000000 : ℝ), (-306946691/500000000 : ℝ), (1291446039/2500000000 : ℝ)] ![(248645542057/20000000000000 : ℝ), (10927436184693/20000000000000 : ℝ), (44119591350243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-144822559/5000000000 : ℝ)|^83 ≤ (248645542057/20000000000000 : ℝ)^67
        have hw : |(-144822559/5000000000 : ℝ)|=(144822559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-306946691/500000000 : ℝ)|^83 ≤ (10927436184693/20000000000000 : ℝ)^67
        have hw : |(-306946691/500000000 : ℝ)|=(306946691/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291446039/2500000000 : ℝ)|^83 ≤ (44119591350243/100000000000000 : ℝ)^67
        have hw : |(1291446039/2500000000 : ℝ)|=(1291446039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2562855533/5000000000 : ℝ)*x 0 + (3733221153/10000000000 : ℝ)*x 1 + (3454312061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2562855533/5000000000 : ℝ)^83 ≤ (43695999011629/100000000000000 : ℝ)^67 := by
    have hnat : (2562855533 : ℕ)^83*100000000000000^67 ≤ 43695999011629^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562855533 5000000000 43695999011629 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3733221153/10000000000 : ℝ)^83 ≤ (14752470653883/50000000000000 : ℝ)^67 := by
    have hnat : (3733221153 : ℕ)^83*50000000000000^67 ≤ 14752470653883^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733221153 10000000000 14752470653883 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3454312061/10000000000 : ℝ)^83 ≤ (26799059663551/100000000000000 : ℝ)^67 := by
    have hnat : (3454312061 : ℕ)^83*100000000000000^67 ≤ 26799059663551^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3454312061 10000000000 26799059663551 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2562855533/5000000000 : ℝ), (3733221153/10000000000 : ℝ), (3454312061/10000000000 : ℝ)] ![(43695999011629/100000000000000 : ℝ), (14752470653883/50000000000000 : ℝ), (26799059663551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2562855533/5000000000 : ℝ)|^83 ≤ (43695999011629/100000000000000 : ℝ)^67
        have hw : |(2562855533/5000000000 : ℝ)|=(2562855533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3733221153/10000000000 : ℝ)|^83 ≤ (14752470653883/50000000000000 : ℝ)^67
        have hw : |(3733221153/10000000000 : ℝ)|=(3733221153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3454312061/10000000000 : ℝ)|^83 ≤ (26799059663551/100000000000000 : ℝ)^67
        have hw : |(3454312061/10000000000 : ℝ)|=(3454312061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (687792549/1250000000 : ℝ)*x 0 + (-3703883877/10000000000 : ℝ)*x 1 + (-3061251437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (687792549/1250000000 : ℝ)^83 ≤ (5963464656579/12500000000000 : ℝ)^67 := by
    have hnat : (687792549 : ℕ)^83*12500000000000^67 ≤ 5963464656579^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687792549 1250000000 5963464656579 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3703883877/10000000000 : ℝ)^83 ≤ (114132728553/390625000000 : ℝ)^67 := by
    have hnat : (3703883877 : ℕ)^83*390625000000^67 ≤ 114132728553^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3703883877 10000000000 114132728553 390625000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3061251437/10000000000 : ℝ)^83 ≤ (5768576057483/25000000000000 : ℝ)^67 := by
    have hnat : (3061251437 : ℕ)^83*25000000000000^67 ≤ 5768576057483^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3061251437 10000000000 5768576057483 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(687792549/1250000000 : ℝ), (-3703883877/10000000000 : ℝ), (-3061251437/10000000000 : ℝ)] ![(5963464656579/12500000000000 : ℝ), (114132728553/390625000000 : ℝ), (5768576057483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(687792549/1250000000 : ℝ)|^83 ≤ (5963464656579/12500000000000 : ℝ)^67
        have hw : |(687792549/1250000000 : ℝ)|=(687792549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3703883877/10000000000 : ℝ)|^83 ≤ (114132728553/390625000000 : ℝ)^67
        have hw : |(-3703883877/10000000000 : ℝ)|=(3703883877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3061251437/10000000000 : ℝ)|^83 ≤ (5768576057483/25000000000000 : ℝ)^67
        have hw : |(-3061251437/10000000000 : ℝ)|=(3061251437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_7 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-83068717/5000000000 : ℝ)*x 0 + (-3866567267/5000000000 : ℝ)*x 1 + (1719333841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83068717/5000000000 : ℝ)^83 ≤ (624459839431/100000000000000 : ℝ)^67 := by
    have hnat : (83068717 : ℕ)^83*100000000000000^67 ≤ 624459839431^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83068717 5000000000 624459839431 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3866567267/5000000000 : ℝ)^83 ≤ (36363377338289/50000000000000 : ℝ)^67 := by
    have hnat : (3866567267 : ℕ)^83*50000000000000^67 ≤ 36363377338289^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3866567267 5000000000 36363377338289 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1719333841/5000000000 : ℝ)^83 ≤ (13324392732969/50000000000000 : ℝ)^67 := by
    have hnat : (1719333841 : ℕ)^83*50000000000000^67 ≤ 13324392732969^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719333841 5000000000 13324392732969 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83068717/5000000000 : ℝ), (-3866567267/5000000000 : ℝ), (1719333841/5000000000 : ℝ)] ![(624459839431/100000000000000 : ℝ), (36363377338289/50000000000000 : ℝ), (13324392732969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83068717/5000000000 : ℝ)|^83 ≤ (624459839431/100000000000000 : ℝ)^67
        have hw : |(-83068717/5000000000 : ℝ)|=(83068717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3866567267/5000000000 : ℝ)|^83 ≤ (36363377338289/50000000000000 : ℝ)^67
        have hw : |(-3866567267/5000000000 : ℝ)|=(3866567267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1719333841/5000000000 : ℝ)|^83 ≤ (13324392732969/50000000000000 : ℝ)^67
        have hw : |(1719333841/5000000000 : ℝ)|=(1719333841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_8 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (386885807/1250000000 : ℝ)*x 0 + (52331/100000 : ℝ)*x 1 + (1981777049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (386885807/1250000000 : ℝ)^83 ≤ (23390656168159/100000000000000 : ℝ)^67 := by
    have hnat : (386885807 : ℕ)^83*100000000000000^67 ≤ 23390656168159^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386885807 1250000000 23390656168159 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52331/100000 : ℝ)^83 ≤ (44832918589553/100000000000000 : ℝ)^67 := by
    have hnat : (52331 : ℕ)^83*100000000000000^67 ≤ 44832918589553^67*100000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52331 100000 44832918589553 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981777049/5000000000 : ℝ)^83 ≤ (7944106308339/25000000000000 : ℝ)^67 := by
    have hnat : (1981777049 : ℕ)^83*25000000000000^67 ≤ 7944106308339^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981777049 5000000000 7944106308339 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(386885807/1250000000 : ℝ), (52331/100000 : ℝ), (1981777049/5000000000 : ℝ)] ![(23390656168159/100000000000000 : ℝ), (44832918589553/100000000000000 : ℝ), (7944106308339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(386885807/1250000000 : ℝ)|^83 ≤ (23390656168159/100000000000000 : ℝ)^67
        have hw : |(386885807/1250000000 : ℝ)|=(386885807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52331/100000 : ℝ)|^83 ≤ (44832918589553/100000000000000 : ℝ)^67
        have hw : |(52331/100000 : ℝ)|=(52331/100000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1981777049/5000000000 : ℝ)|^83 ≤ (7944106308339/25000000000000 : ℝ)^67
        have hw : |(1981777049/5000000000 : ℝ)|=(1981777049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_9 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2369100593/5000000000 : ℝ)*x 0 + (-1649783393/5000000000 : ℝ)*x 1 + (-4288911171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2369100593/5000000000 : ℝ)^83 ≤ (3964131599551/10000000000000 : ℝ)^67 := by
    have hnat : (2369100593 : ℕ)^83*10000000000000^67 ≤ 3964131599551^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369100593 5000000000 3964131599551 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1649783393/5000000000 : ℝ)^83 ≤ (6329968813459/25000000000000 : ℝ)^67 := by
    have hnat : (1649783393 : ℕ)^83*25000000000000^67 ≤ 6329968813459^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649783393 5000000000 6329968813459 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4288911171/10000000000 : ℝ)^83 ≤ (1751940437039/5000000000000 : ℝ)^67 := by
    have hnat : (4288911171 : ℕ)^83*5000000000000^67 ≤ 1751940437039^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288911171 10000000000 1751940437039 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2369100593/5000000000 : ℝ), (-1649783393/5000000000 : ℝ), (-4288911171/10000000000 : ℝ)] ![(3964131599551/10000000000000 : ℝ), (6329968813459/25000000000000 : ℝ), (1751940437039/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2369100593/5000000000 : ℝ)|^83 ≤ (3964131599551/10000000000000 : ℝ)^67
        have hw : |(2369100593/5000000000 : ℝ)|=(2369100593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1649783393/5000000000 : ℝ)|^83 ≤ (6329968813459/25000000000000 : ℝ)^67
        have hw : |(-1649783393/5000000000 : ℝ)|=(1649783393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4288911171/10000000000 : ℝ)|^83 ≤ (1751940437039/5000000000000 : ℝ)^67
        have hw : |(-4288911171/10000000000 : ℝ)|=(4288911171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_13 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5079573627/10000000000 : ℝ)*x 0 + (3687803/5000000000 : ℝ)*x 1 + (3166170007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5079573627/10000000000 : ℝ)^83 ≤ (43209282323709/100000000000000 : ℝ)^67 := by
    have hnat : (5079573627 : ℕ)^83*100000000000000^67 ≤ 43209282323709^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079573627 10000000000 43209282323709 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3687803/5000000000 : ℝ)^83 ≤ (3294193537/25000000000000 : ℝ)^67 := by
    have hnat : (3687803 : ℕ)^83*25000000000000^67 ≤ 3294193537^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3687803 5000000000 3294193537 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3166170007/5000000000 : ℝ)^83 ≤ (28388770443793/50000000000000 : ℝ)^67 := by
    have hnat : (3166170007 : ℕ)^83*50000000000000^67 ≤ 28388770443793^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3166170007 5000000000 28388770443793 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5079573627/10000000000 : ℝ), (3687803/5000000000 : ℝ), (3166170007/5000000000 : ℝ)] ![(43209282323709/100000000000000 : ℝ), (3294193537/25000000000000 : ℝ), (28388770443793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5079573627/10000000000 : ℝ)|^83 ≤ (43209282323709/100000000000000 : ℝ)^67
        have hw : |(5079573627/10000000000 : ℝ)|=(5079573627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3687803/5000000000 : ℝ)|^83 ≤ (3294193537/25000000000000 : ℝ)^67
        have hw : |(3687803/5000000000 : ℝ)|=(3687803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3166170007/5000000000 : ℝ)|^83 ≤ (28388770443793/50000000000000 : ℝ)^67
        have hw : |(3166170007/5000000000 : ℝ)|=(3166170007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_14 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (299/10000000000 : ℝ)*x 0 + (-146309199/312500000 : ℝ)*x 1 + (3352318517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (299/10000000000 : ℝ)^83 ≤ (47733/100000000000000 : ℝ)^67 := by
    have hnat : (299 : ℕ)^83*100000000000000^67 ≤ 47733^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299 10000000000 47733 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146309199/312500000 : ℝ)^83 ≤ (4882321082349/12500000000000 : ℝ)^67 := by
    have hnat : (146309199 : ℕ)^83*12500000000000^67 ≤ 4882321082349^67*312500000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146309199 312500000 4882321082349 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3352318517/5000000000 : ℝ)^83 ≤ (7617678909911/12500000000000 : ℝ)^67 := by
    have hnat : (3352318517 : ℕ)^83*12500000000000^67 ≤ 7617678909911^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3352318517 5000000000 7617678909911 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(299/10000000000 : ℝ), (-146309199/312500000 : ℝ), (3352318517/5000000000 : ℝ)] ![(47733/100000000000000 : ℝ), (4882321082349/12500000000000 : ℝ), (7617678909911/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(299/10000000000 : ℝ)|^83 ≤ (47733/100000000000000 : ℝ)^67
        have hw : |(299/10000000000 : ℝ)|=(299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-146309199/312500000 : ℝ)|^83 ≤ (4882321082349/12500000000000 : ℝ)^67
        have hw : |(-146309199/312500000 : ℝ)|=(146309199/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3352318517/5000000000 : ℝ)|^83 ≤ (7617678909911/12500000000000 : ℝ)^67
        have hw : |(3352318517/5000000000 : ℝ)|=(3352318517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_15 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (193988021/625000000 : ℝ)*x 0 + (4615005789/10000000000 : ℝ)*x 1 + (4594673617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (193988021/625000000 : ℝ)^83 ≤ (11736169333691/50000000000000 : ℝ)^67 := by
    have hnat : (193988021 : ℕ)^83*50000000000000^67 ≤ 11736169333691^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193988021 625000000 11736169333691 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4615005789/10000000000 : ℝ)^83 ≤ (38368478580479/100000000000000 : ℝ)^67 := by
    have hnat : (4615005789 : ℕ)^83*100000000000000^67 ≤ 38368478580479^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4615005789 10000000000 38368478580479 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4594673617/10000000000 : ℝ)^83 ≤ (19079591365387/50000000000000 : ℝ)^67 := by
    have hnat : (4594673617 : ℕ)^83*50000000000000^67 ≤ 19079591365387^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4594673617 10000000000 19079591365387 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(193988021/625000000 : ℝ), (4615005789/10000000000 : ℝ), (4594673617/10000000000 : ℝ)] ![(11736169333691/50000000000000 : ℝ), (38368478580479/100000000000000 : ℝ), (19079591365387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(193988021/625000000 : ℝ)|^83 ≤ (11736169333691/50000000000000 : ℝ)^67
        have hw : |(193988021/625000000 : ℝ)|=(193988021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4615005789/10000000000 : ℝ)|^83 ≤ (38368478580479/100000000000000 : ℝ)^67
        have hw : |(4615005789/10000000000 : ℝ)|=(4615005789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4594673617/10000000000 : ℝ)|^83 ≤ (19079591365387/50000000000000 : ℝ)^67
        have hw : |(4594673617/10000000000 : ℝ)|=(4594673617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_16 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3398528119/5000000000 : ℝ)*x 0 + (-2626084441/10000000000 : ℝ)*x 1 + (-521907073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3398528119/5000000000 : ℝ)^83 ≤ (495870270501/800000000000 : ℝ)^67 := by
    have hnat : (3398528119 : ℕ)^83*800000000000^67 ≤ 495870270501^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3398528119 5000000000 495870270501 800000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626084441/10000000000 : ℝ)^83 ≤ (19082537923197/100000000000000 : ℝ)^67 := by
    have hnat : (2626084441 : ℕ)^83*100000000000000^67 ≤ 19082537923197^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626084441 10000000000 19082537923197 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521907073/2000000000 : ℝ)^83 ≤ (18933678252673/100000000000000 : ℝ)^67 := by
    have hnat : (521907073 : ℕ)^83*100000000000000^67 ≤ 18933678252673^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521907073 2000000000 18933678252673 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3398528119/5000000000 : ℝ), (-2626084441/10000000000 : ℝ), (-521907073/2000000000 : ℝ)] ![(495870270501/800000000000 : ℝ), (19082537923197/100000000000000 : ℝ), (18933678252673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3398528119/5000000000 : ℝ)|^83 ≤ (495870270501/800000000000 : ℝ)^67
        have hw : |(3398528119/5000000000 : ℝ)|=(3398528119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2626084441/10000000000 : ℝ)|^83 ≤ (19082537923197/100000000000000 : ℝ)^67
        have hw : |(-2626084441/10000000000 : ℝ)|=(2626084441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-521907073/2000000000 : ℝ)|^83 ≤ (18933678252673/100000000000000 : ℝ)^67
        have hw : |(-521907073/2000000000 : ℝ)|=(521907073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_20 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2067007833/2500000000 : ℝ)*x 0 + (-15510871/1000000000 : ℝ)*x 1 + (277339439/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067007833/2500000000 : ℝ)^83 ≤ (79009123765747/100000000000000 : ℝ)^67 := by
    have hnat : (2067007833 : ℕ)^83*100000000000000^67 ≤ 79009123765747^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067007833 2500000000 79009123765747 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15510871/1000000000 : ℝ)^83 ≤ (286760487027/50000000000000 : ℝ)^67 := by
    have hnat : (15510871 : ℕ)^83*50000000000000^67 ≤ 286760487027^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15510871 1000000000 286760487027 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277339439/1000000000 : ℝ)^83 ≤ (20417355250307/100000000000000 : ℝ)^67 := by
    have hnat : (277339439 : ℕ)^83*100000000000000^67 ≤ 20417355250307^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277339439 1000000000 20417355250307 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2067007833/2500000000 : ℝ), (-15510871/1000000000 : ℝ), (277339439/1000000000 : ℝ)] ![(79009123765747/100000000000000 : ℝ), (286760487027/50000000000000 : ℝ), (20417355250307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2067007833/2500000000 : ℝ)|^83 ≤ (79009123765747/100000000000000 : ℝ)^67
        have hw : |(2067007833/2500000000 : ℝ)|=(2067007833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15510871/1000000000 : ℝ)|^83 ≤ (286760487027/50000000000000 : ℝ)^67
        have hw : |(-15510871/1000000000 : ℝ)|=(15510871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(277339439/1000000000 : ℝ)|^83 ≤ (20417355250307/100000000000000 : ℝ)^67
        have hw : |(277339439/1000000000 : ℝ)|=(277339439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_21 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-87056693/2000000000 : ℝ)*x 0 + (-8221283381/10000000000 : ℝ)*x 1 + (267066827/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87056693/2000000000 : ℝ)^83 ≤ (1029610213089/50000000000000 : ℝ)^67 := by
    have hnat : (87056693 : ℕ)^83*50000000000000^67 ≤ 1029610213089^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87056693 2000000000 1029610213089 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8221283381/10000000000 : ℝ)^83 ≤ (78456095558373/100000000000000 : ℝ)^67 := by
    have hnat : (8221283381 : ℕ)^83*100000000000000^67 ≤ 78456095558373^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8221283381 10000000000 78456095558373 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267066827/1000000000 : ℝ)^83 ≤ (4871170998487/25000000000000 : ℝ)^67 := by
    have hnat : (267066827 : ℕ)^83*25000000000000^67 ≤ 4871170998487^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267066827 1000000000 4871170998487 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87056693/2000000000 : ℝ), (-8221283381/10000000000 : ℝ), (267066827/1000000000 : ℝ)] ![(1029610213089/50000000000000 : ℝ), (78456095558373/100000000000000 : ℝ), (4871170998487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87056693/2000000000 : ℝ)|^83 ≤ (1029610213089/50000000000000 : ℝ)^67
        have hw : |(-87056693/2000000000 : ℝ)|=(87056693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8221283381/10000000000 : ℝ)|^83 ≤ (78456095558373/100000000000000 : ℝ)^67
        have hw : |(-8221283381/10000000000 : ℝ)|=(8221283381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(267066827/1000000000 : ℝ)|^83 ≤ (4871170998487/25000000000000 : ℝ)^67
        have hw : |(267066827/1000000000 : ℝ)|=(267066827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_22 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6649631763/10000000000 : ℝ)*x 0 + (3140855743/10000000000 : ℝ)*x 1 + (2261541217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6649631763/10000000000 : ℝ)^83 ≤ (60322676668667/100000000000000 : ℝ)^67 := by
    have hnat : (6649631763 : ℕ)^83*100000000000000^67 ≤ 60322676668667^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6649631763 10000000000 60322676668667 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3140855743/10000000000 : ℝ)^83 ≤ (11909953111931/50000000000000 : ℝ)^67 := by
    have hnat : (3140855743 : ℕ)^83*50000000000000^67 ≤ 11909953111931^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3140855743 10000000000 11909953111931 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261541217/10000000000 : ℝ)^83 ≤ (7928708543161/50000000000000 : ℝ)^67 := by
    have hnat : (2261541217 : ℕ)^83*50000000000000^67 ≤ 7928708543161^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261541217 10000000000 7928708543161 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6649631763/10000000000 : ℝ), (3140855743/10000000000 : ℝ), (2261541217/10000000000 : ℝ)] ![(60322676668667/100000000000000 : ℝ), (11909953111931/50000000000000 : ℝ), (7928708543161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6649631763/10000000000 : ℝ)|^83 ≤ (60322676668667/100000000000000 : ℝ)^67
        have hw : |(6649631763/10000000000 : ℝ)|=(6649631763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3140855743/10000000000 : ℝ)|^83 ≤ (11909953111931/50000000000000 : ℝ)^67
        have hw : |(3140855743/10000000000 : ℝ)|=(3140855743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261541217/10000000000 : ℝ)|^83 ≤ (7928708543161/50000000000000 : ℝ)^67
        have hw : |(2261541217/10000000000 : ℝ)|=(2261541217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_23 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2250849271/10000000000 : ℝ)*x 0 + (-6781632263/10000000000 : ℝ)*x 1 + (-1495805811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2250849271/10000000000 : ℝ)^83 ≤ (15764596894183/100000000000000 : ℝ)^67 := by
    have hnat : (2250849271 : ℕ)^83*100000000000000^67 ≤ 15764596894183^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250849271 10000000000 15764596894183 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6781632263/10000000000 : ℝ)^83 ≤ (61809587456099/100000000000000 : ℝ)^67 := by
    have hnat : (6781632263 : ℕ)^83*100000000000000^67 ≤ 61809587456099^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6781632263 10000000000 61809587456099 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1495805811/5000000000 : ℝ)^83 ≤ (22425815630641/100000000000000 : ℝ)^67 := by
    have hnat : (1495805811 : ℕ)^83*100000000000000^67 ≤ 22425815630641^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1495805811 5000000000 22425815630641 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2250849271/10000000000 : ℝ), (-6781632263/10000000000 : ℝ), (-1495805811/5000000000 : ℝ)] ![(15764596894183/100000000000000 : ℝ), (61809587456099/100000000000000 : ℝ), (22425815630641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2250849271/10000000000 : ℝ)|^83 ≤ (15764596894183/100000000000000 : ℝ)^67
        have hw : |(2250849271/10000000000 : ℝ)|=(2250849271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6781632263/10000000000 : ℝ)|^83 ≤ (61809587456099/100000000000000 : ℝ)^67
        have hw : |(-6781632263/10000000000 : ℝ)|=(6781632263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1495805811/5000000000 : ℝ)|^83 ≤ (22425815630641/100000000000000 : ℝ)^67
        have hw : |(-1495805811/5000000000 : ℝ)|=(1495805811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s0_27 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1635786167/2000000000 : ℝ)*x 0 + (949/2500000000 : ℝ)*x 1 + (2950458923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1635786167/2000000000 : ℝ)^83 ≤ (7795571282767/10000000000000 : ℝ)^67 := by
    have hnat : (1635786167 : ℕ)^83*10000000000000^67 ≤ 7795571282767^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1635786167 2000000000 7795571282767 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (949/2500000000 : ℝ)^83 ≤ (277953/25000000000000 : ℝ)^67 := by
    have hnat : (949 : ℕ)^83*25000000000000^67 ≤ 277953^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949 2500000000 277953 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2950458923/10000000000 : ℝ)^83 ≤ (2755535755727/12500000000000 : ℝ)^67 := by
    have hnat : (2950458923 : ℕ)^83*12500000000000^67 ≤ 2755535755727^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2950458923 10000000000 2755535755727 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1635786167/2000000000 : ℝ), (949/2500000000 : ℝ), (2950458923/10000000000 : ℝ)] ![(7795571282767/10000000000000 : ℝ), (277953/25000000000000 : ℝ), (2755535755727/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1635786167/2000000000 : ℝ)|^83 ≤ (7795571282767/10000000000000 : ℝ)^67
        have hw : |(1635786167/2000000000 : ℝ)|=(1635786167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(949/2500000000 : ℝ)|^83 ≤ (277953/25000000000000 : ℝ)^67
        have hw : |(949/2500000000 : ℝ)|=(949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2950458923/10000000000 : ℝ)|^83 ≤ (2755535755727/12500000000000 : ℝ)^67
        have hw : |(2950458923/10000000000 : ℝ)|=(2950458923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s1_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-341302257/2000000000 : ℝ)*x 0 + (-5083902551/10000000000 : ℝ)*x 1 + (2650638867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341302257/2000000000 : ℝ)^83 ≤ (11187479400287/100000000000000 : ℝ)^67 := by
    have hnat : (341302257 : ℕ)^83*100000000000000^67 ≤ 11187479400287^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341302257 2000000000 11187479400287 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083902551/10000000000 : ℝ)^83 ≤ (1351715769653/3125000000000 : ℝ)^67 := by
    have hnat : (5083902551 : ℕ)^83*3125000000000^67 ≤ 1351715769653^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083902551 10000000000 1351715769653 3125000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2650638867/5000000000 : ℝ)^83 ≤ (22778807973923/50000000000000 : ℝ)^67 := by
    have hnat : (2650638867 : ℕ)^83*50000000000000^67 ≤ 22778807973923^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650638867 5000000000 22778807973923 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-341302257/2000000000 : ℝ), (-5083902551/10000000000 : ℝ), (2650638867/5000000000 : ℝ)] ![(11187479400287/100000000000000 : ℝ), (1351715769653/3125000000000 : ℝ), (22778807973923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-341302257/2000000000 : ℝ)|^83 ≤ (11187479400287/100000000000000 : ℝ)^67
        have hw : |(-341302257/2000000000 : ℝ)|=(341302257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5083902551/10000000000 : ℝ)|^83 ≤ (1351715769653/3125000000000 : ℝ)^67
        have hw : |(-5083902551/10000000000 : ℝ)|=(5083902551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2650638867/5000000000 : ℝ)|^83 ≤ (22778807973923/50000000000000 : ℝ)^67
        have hw : |(2650638867/5000000000 : ℝ)|=(2650638867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s1_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2482975859/5000000000 : ℝ)*x 0 + (158232047/400000000 : ℝ)*x 1 + (17003829/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2482975859/5000000000 : ℝ)^83 ≤ (10503791242797/25000000000000 : ℝ)^67 := by
    have hnat : (2482975859 : ℕ)^83*25000000000000^67 ≤ 10503791242797^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482975859 5000000000 10503791242797 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158232047/400000000 : ℝ)^83 ≤ (15849721765273/50000000000000 : ℝ)^67 := by
    have hnat : (158232047 : ℕ)^83*50000000000000^67 ≤ 15849721765273^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158232047 400000000 15849721765273 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17003829/50000000 : ℝ)^83 ≤ (26285391490741/100000000000000 : ℝ)^67 := by
    have hnat : (17003829 : ℕ)^83*100000000000000^67 ≤ 26285391490741^67*50000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17003829 50000000 26285391490741 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2482975859/5000000000 : ℝ), (158232047/400000000 : ℝ), (17003829/50000000 : ℝ)] ![(10503791242797/25000000000000 : ℝ), (15849721765273/50000000000000 : ℝ), (26285391490741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2482975859/5000000000 : ℝ)|^83 ≤ (10503791242797/25000000000000 : ℝ)^67
        have hw : |(2482975859/5000000000 : ℝ)|=(2482975859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158232047/400000000 : ℝ)|^83 ≤ (15849721765273/50000000000000 : ℝ)^67
        have hw : |(158232047/400000000 : ℝ)|=(158232047/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17003829/50000000 : ℝ)|^83 ≤ (26285391490741/100000000000000 : ℝ)^67
        have hw : |(17003829/50000000 : ℝ)|=(17003829/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s1_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (969158811/2000000000 : ℝ)*x 0 + (-4059943317/10000000000 : ℝ)*x 1 + (-3423585051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (969158811/2000000000 : ℝ)^83 ≤ (5094930194263/12500000000000 : ℝ)^67 := by
    have hnat : (969158811 : ℕ)^83*12500000000000^67 ≤ 5094930194263^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969158811 2000000000 5094930194263 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4059943317/10000000000 : ℝ)^83 ≤ (32736496730847/100000000000000 : ℝ)^67 := by
    have hnat : (4059943317 : ℕ)^83*100000000000000^67 ≤ 32736496730847^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4059943317 10000000000 32736496730847 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3423585051/10000000000 : ℝ)^83 ≤ (26504061703081/100000000000000 : ℝ)^67 := by
    have hnat : (3423585051 : ℕ)^83*100000000000000^67 ≤ 26504061703081^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3423585051 10000000000 26504061703081 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(969158811/2000000000 : ℝ), (-4059943317/10000000000 : ℝ), (-3423585051/10000000000 : ℝ)] ![(5094930194263/12500000000000 : ℝ), (32736496730847/100000000000000 : ℝ), (26504061703081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(969158811/2000000000 : ℝ)|^83 ≤ (5094930194263/12500000000000 : ℝ)^67
        have hw : |(969158811/2000000000 : ℝ)|=(969158811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4059943317/10000000000 : ℝ)|^83 ≤ (32736496730847/100000000000000 : ℝ)^67
        have hw : |(-4059943317/10000000000 : ℝ)|=(4059943317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3423585051/10000000000 : ℝ)|^83 ≤ (26504061703081/100000000000000 : ℝ)^67
        have hw : |(-3423585051/10000000000 : ℝ)|=(3423585051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321047_s1_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6043689137/10000000000 : ℝ)*x 0 + (-1646615333/10000000000 : ℝ)*x 1 + (4354900801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6043689137/10000000000 : ℝ)^83 ≤ (53589012959897/100000000000000 : ℝ)^67 := by
    have hnat : (6043689137 : ℕ)^83*100000000000000^67 ≤ 53589012959897^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6043689137 10000000000 53589012959897 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1646615333/10000000000 : ℝ)^83 ≤ (10703102505543/100000000000000 : ℝ)^67 := by
    have hnat : (1646615333 : ℕ)^83*100000000000000^67 ≤ 10703102505543^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1646615333 10000000000 10703102505543 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4354900801/10000000000 : ℝ)^83 ≤ (8926971129163/25000000000000 : ℝ)^67 := by
    have hnat : (4354900801 : ℕ)^83*25000000000000^67 ≤ 8926971129163^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354900801 10000000000 8926971129163 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6043689137/10000000000 : ℝ), (-1646615333/10000000000 : ℝ), (4354900801/10000000000 : ℝ)] ![(53589012959897/100000000000000 : ℝ), (10703102505543/100000000000000 : ℝ), (8926971129163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6043689137/10000000000 : ℝ)|^83 ≤ (53589012959897/100000000000000 : ℝ)^67
        have hw : |(6043689137/10000000000 : ℝ)|=(6043689137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1646615333/10000000000 : ℝ)|^83 ≤ (10703102505543/100000000000000 : ℝ)^67
        have hw : |(-1646615333/10000000000 : ℝ)|=(1646615333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4354900801/10000000000 : ℝ)|^83 ≤ (8926971129163/25000000000000 : ℝ)^67
        have hw : |(4354900801/10000000000 : ℝ)|=(4354900801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321047 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80491/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80491/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (168549/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-144822559/5000000000 : ℝ)*X 0 0+(-306946691/500000000 : ℝ)*X 0 1+(1291446039/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2562855533/5000000000 : ℝ)*X 1 0+(3733221153/10000000000 : ℝ)*X 1 1+(3454312061/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((687792549/1250000000 : ℝ)*X 2 0+(-3703883877/10000000000 : ℝ)*X 2 1+(-3061251437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-83068717/5000000000 : ℝ)*X 0 0+(-3866567267/5000000000 : ℝ)*X 0 1+(1719333841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((386885807/1250000000 : ℝ)*X 1 0+(52331/100000 : ℝ)*X 1 1+(1981777049/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2369100593/5000000000 : ℝ)*X 2 0+(-1649783393/5000000000 : ℝ)*X 2 1+(-4288911171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((5079573627/10000000000 : ℝ)*X 0 0+(3687803/5000000000 : ℝ)*X 0 1+(3166170007/5000000000 : ℝ)*X 0 2+(5079573627/10000000000 : ℝ)*X 1 0+(3687803/5000000000 : ℝ)*X 1 1+(3166170007/5000000000 : ℝ)*X 1 2+(5079573627/10000000000 : ℝ)*X 2 0+(3687803/5000000000 : ℝ)*X 2 1+(3166170007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((299/10000000000 : ℝ)*X 0 0+(-146309199/312500000 : ℝ)*X 0 1+(3352318517/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((193988021/625000000 : ℝ)*X 1 0+(4615005789/10000000000 : ℝ)*X 1 1+(4594673617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3398528119/5000000000 : ℝ)*X 2 0+(-2626084441/10000000000 : ℝ)*X 2 1+(-521907073/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2067007833/2500000000 : ℝ)*X 0 0+(-15510871/1000000000 : ℝ)*X 0 1+(277339439/1000000000 : ℝ)*X 0 2+(2067007833/2500000000 : ℝ)*X 1 0+(-15510871/1000000000 : ℝ)*X 1 1+(277339439/1000000000 : ℝ)*X 1 2+(2067007833/2500000000 : ℝ)*X 2 0+(-15510871/1000000000 : ℝ)*X 2 1+(277339439/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-87056693/2000000000 : ℝ)*X 0 0+(-8221283381/10000000000 : ℝ)*X 0 1+(267066827/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6649631763/10000000000 : ℝ)*X 1 0+(3140855743/10000000000 : ℝ)*X 1 1+(2261541217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2250849271/10000000000 : ℝ)*X 2 0+(-6781632263/10000000000 : ℝ)*X 2 1+(-1495805811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1635786167/2000000000 : ℝ)*X 0 0+(949/2500000000 : ℝ)*X 0 1+(2950458923/10000000000 : ℝ)*X 0 2+(1635786167/2000000000 : ℝ)*X 1 0+(949/2500000000 : ℝ)*X 1 1+(2950458923/10000000000 : ℝ)*X 1 2+(1635786167/2000000000 : ℝ)*X 2 0+(949/2500000000 : ℝ)*X 2 1+(2950458923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((59711/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(59711/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4381168629649257795597/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (396354505007/1000000000000 : ℝ)*(base3) + (23160587269/20000000000 : ℝ)*(base7) + (288427673411/1000000000000 : ℝ)*(base50) + (2137873012903/1000000000000 : ℝ)*(major_s0_0) + (2137873012903/1000000000000 : ℝ)*(major_s0_1) + (2137873012903/1000000000000 : ℝ)*(major_s0_2) + (14105101/1000000000000 : ℝ)*(sp_s0_0) + (10645937/1000000000000 : ℝ)*(sp_s0_2) + (2501994838723/1000000000000 : ℝ)*(sp_s0_7) + (1449135722547/500000000000 : ℝ)*(sp_s0_8) + (2501971406479/1000000000000 : ℝ)*(sp_s0_9) + (188479046159/100000000000 : ℝ)*(sp_s0_13) + (11500467/125000000000 : ℝ)*(sp_s0_15) + (26891407/1000000000000 : ℝ)*(sp_s0_23) + (1123115603147/1000000000000 : ℝ)*(f.failure) + (156375558989/62500000000 : ℝ)*(f.sum) + (1509169004113349/5000000000000000000000000000 : ℝ)*base63 + (1344348519484661/5000000000000000000000000000 : ℝ)*base64 + (1165895751484661/5000000000000000000000000000 : ℝ)*base66 + (4758633529113349/10000000000000000000000000000 : ℝ)*base69 + (4701209974144027/10000000000000000000000000000 : ℝ)*base71 + (2672355007515339/5000000000000000000000000000 : ℝ)*base73 + (9591837994113349/10000000000000000000000000000 : ℝ)*base75 + (6507734636886651/10000000000000000000000000000 : ℝ)*base76 + (1766347632484661/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (3891/6250000000000000 : ℝ)*base86 + (3891/6250000000000000 : ℝ)*base88 + (3891/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-26371/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-26371/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5317110561621327287079/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84194525147/100000000000 : ℝ)*(base7) + (71413499059/125000000000 : ℝ)*(base40) + (852879/250000000000 : ℝ)*(base49) + (24981426733/200000000000 : ℝ)*(base59) + (539226483571/250000000000 : ℝ)*(major_s0_0) + (539226483571/250000000000 : ℝ)*(major_s0_1) + (539226483571/250000000000 : ℝ)*(major_s0_2) + (35904767/1000000000000 : ℝ)*(sp_s0_1) + (45343/25000000000 : ℝ)*(sp_s0_9) + (541532905209/200000000000 : ℝ)*(sp_s0_14) + (2707628621277/1000000000000 : ℝ)*(sp_s0_15) + (676915678081/250000000000 : ℝ)*(sp_s0_16) + (1974787134107/1000000000000 : ℝ)*(sp_s0_20) + (4258179/15625000000 : ℝ)*(sp_s0_27) + (283278601523/250000000000 : ℝ)*(f.failure) + (541532905209/200000000000 : ℝ)*(f.sum) + (672891111341807/1250000000000000000000000000 : ℝ)*base62 + (124518468869623/1250000000000000000000000000 : ℝ)*base65 + (286425993880377/1250000000000000000000000000 : ℝ)*base66 + (617260138466807/2500000000000000000000000000 : ℝ)*base68 + (481351677772439/2500000000000000000000000000 : ℝ)*base71 + (232612360369623/1250000000000000000000000000 : ℝ)*base73 + (323543222966807/2500000000000000000000000000 : ℝ)*base74 + (718307444466807/2500000000000000000000000000 : ℝ)*base76 + (98240802755377/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (381/1562500000000000 : ℝ)*base87 + (381/1562500000000000 : ℝ)*base89 + (381/1562500000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34849/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34849/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (39984455017877906414433/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23419614883/1000000000000 : ℝ)*(base3) + (11954013823/10000000000 : ℝ)*(base7) + (3069279/1000000000000 : ℝ)*(base34) + (96145733357/500000000000 : ℝ)*(base40) + (7006283/1000000000000 : ℝ)*(base43) + (1826599383/15625000000 : ℝ)*(base50) + (56025854263/31250000000 : ℝ)*(major_s0_0) + (448205849853/250000000000 : ℝ)*(major_s0_1) + (358566081139/200000000000 : ℝ)*(major_s0_2) + (322811/50000000000 : ℝ)*(sp_s0_2) + (1972185662353/1000000000000 : ℝ)*(sp_s0_21) + (997807676399/500000000000 : ℝ)*(sp_s0_22) + (493045568853/250000000000 : ℝ)*(sp_s0_23) + (13211429671/6250000000 : ℝ)*(sp_s0_27) + (470925024611/500000000000 : ℝ)*(f.failure) + (394439147583/200000000000 : ℝ)*(f.sum) + (3163833731410519/10000000000000000000000000000 : ℝ)*base62 + (432192402153607/1000000000000000000000000000 : ℝ)*base65 + (481153281414311/1250000000000000000000000000 : ℝ)*base66 + (1559881295794263/2000000000000000000000000000 : ℝ)*base68 + (1484712718215699/5000000000000000000000000000 : ℝ)*base71 + (117915693203731/156250000000000000000000000 : ℝ)*base72 + (1541487940859801/2500000000000000000000000000 : ℝ)*base74 + (263230611184229/312500000000000000000000000 : ℝ)*base77 + (713824557044159/1250000000000000000000000000 : ℝ)*base78 + (3/48828125000000 : ℝ)*base87 + (3/48828125000000 : ℝ)*base89 + (3/48828125000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (59711/100000 : ℝ) ^ (81/16 : ℝ) ≤ (918724149022956621/12500000000000000000 : ℝ) := by
    have hpowers : (59711/100000 : ℝ)^81 ≤ (918724149022956621/12500000000000000000 : ℝ)^16 := by
      have hnat : (59711 : ℕ)^81*12500000000000000000^16 ≤ 918724149022956621^16*100000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59711 100000 918724149022956621 12500000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59711/100000 : ℝ)) (X := (918724149022956621/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (13418724149022956621/12500000000000000000 : ℝ) ≤ (5070539781618187/5000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (13418724149022956621/12500000000000000000 : ℝ)^16 ≤ (5070539781618187/5000000000000000 : ℝ)^81 := by
      have hnat : (13418724149022956621 : ℕ)^16*5000000000000000^81 ≤ 5070539781618187^81*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13418724149022956621 12500000000000000000 5070539781618187 5000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5070539781618187/5000000000000000 : ℝ)) (X := (13418724149022956621/12500000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (7168724149022956621/6250000000000000000 : ℝ) ≤ (10274609006238491/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (7168724149022956621/6250000000000000000 : ℝ)^16 ≤ (10274609006238491/10000000000000000 : ℝ)^81 := by
      have hnat : (7168724149022956621 : ℕ)^16*10000000000000000^81 ≤ 10274609006238491^81*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7168724149022956621 6250000000000000000 10274609006238491 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10274609006238491/10000000000000000 : ℝ)) (X := (7168724149022956621/6250000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(70539781618187/2985550000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(133529443002117/5971100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (59711/100000 : ℝ)) (alpha := (70539781618187/2985550000000000 : ℝ)) (beta := (133529443002117/5971100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (59711/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(70539781618187/2985550000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(133529443002117/5971100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (26371/50000 : ℝ) ^ (81/16 : ℝ) ≤ (1960594425695945723/50000000000000000000 : ℝ) := by
    have hpowers : (26371/50000 : ℝ)^81 ≤ (1960594425695945723/50000000000000000000 : ℝ)^16 := by
      have hnat : (26371 : ℕ)^81*50000000000000000000^16 ≤ 1960594425695945723^16*50000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26371 50000 1960594425695945723 50000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26371/50000 : ℝ)) (X := (1960594425695945723/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (51960594425695945723/50000000000000000000 : ℝ) ≤ (5038132452425147/5000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (51960594425695945723/50000000000000000000 : ℝ)^16 ≤ (5038132452425147/5000000000000000 : ℝ)^81 := by
      have hnat : (51960594425695945723 : ℕ)^16*5000000000000000^81 ≤ 5038132452425147^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51960594425695945723 50000000000000000000 5038132452425147 5000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5038132452425147/5000000000000000 : ℝ)) (X := (51960594425695945723/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (26960594425695945723/25000000000000000000 : ℝ) ≤ (79298862868177/78125000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (26960594425695945723/25000000000000000000 : ℝ)^16 ≤ (79298862868177/78125000000000 : ℝ)^81 := by
      have hnat : (26960594425695945723 : ℕ)^16*78125000000000^81 ≤ 79298862868177^81*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26960594425695945723 25000000000000000000 79298862868177 78125000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (79298862868177/78125000000000 : ℝ)) (X := (26960594425695945723/25000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(38132452425147/2637100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(36994771138181/2637100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (26371/50000 : ℝ)) (alpha := (38132452425147/2637100000000000 : ℝ)) (beta := (36994771138181/2637100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (26371/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(38132452425147/2637100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(36994771138181/2637100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (34849/50000 : ℝ) ^ (81/16 : ℝ) ≤ (2010077782189371941/12500000000000000000 : ℝ) := by
    have hpowers : (34849/50000 : ℝ)^81 ≤ (2010077782189371941/12500000000000000000 : ℝ)^16 := by
      have hnat : (34849 : ℕ)^81*12500000000000000000^16 ≤ 2010077782189371941^16*50000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34849 50000 2010077782189371941 12500000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34849/50000 : ℝ)) (X := (2010077782189371941/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (14510077782189371941/12500000000000000000 : ℝ) ≤ (411957141762917/400000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (14510077782189371941/12500000000000000000 : ℝ)^16 ≤ (411957141762917/400000000000000 : ℝ)^81 := by
      have hnat : (14510077782189371941 : ℕ)^16*400000000000000^81 ≤ 411957141762917^81*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14510077782189371941 12500000000000000000 411957141762917 400000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (411957141762917/400000000000000 : ℝ)) (X := (14510077782189371941/12500000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (8260077782189371941/6250000000000000000 : ℝ) ≤ (330196011536037/312500000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (8260077782189371941/6250000000000000000 : ℝ)^16 ≤ (330196011536037/312500000000000 : ℝ)^81 := by
      have hnat : (8260077782189371941 : ℕ)^16*312500000000000^81 ≤ 330196011536037^81*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8260077782189371941 6250000000000000000 330196011536037 312500000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (330196011536037/312500000000000 : ℝ)) (X := (8260077782189371941/6250000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(11957141762917/278792000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(267343825080259/6969800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (34849/50000 : ℝ)) (alpha := (11957141762917/278792000000000 : ℝ)) (beta := (267343825080259/6969800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (34849/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(11957141762917/278792000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(267343825080259/6969800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-341302257/2000000000 : ℝ)*X 0 0+(-5083902551/10000000000 : ℝ)*X 0 1+(2650638867/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2482975859/5000000000 : ℝ)*X 1 0+(158232047/400000000 : ℝ)*X 1 1+(17003829/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((969158811/2000000000 : ℝ)*X 2 0+(-4059943317/10000000000 : ℝ)*X 2 1+(-3423585051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6043689137/10000000000 : ℝ)*X 0 0+(-1646615333/10000000000 : ℝ)*X 0 1+(4354900801/10000000000 : ℝ)*X 0 2+(6043689137/10000000000 : ℝ)*X 1 0+(-1646615333/10000000000 : ℝ)*X 1 1+(4354900801/10000000000 : ℝ)*X 1 2+(6043689137/10000000000 : ℝ)*X 2 0+(-1646615333/10000000000 : ℝ)*X 2 1+(4354900801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321047_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-26316/3125 : ℝ) < ((-11897/6250 : ℝ)*P 0+(-11897/6250 : ℝ)*P 1+(-11897/6250 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-26316/3125 : ℝ) < (-183095634488437441553944330324381239/21949834751627600000000000000000000 : ℝ) := by norm_num
    linear_combination (126441/200000000000 : ℝ)*(base5) + (88441/200000000000 : ℝ)*(base10) + (307773/1000000000000 : ℝ)*(base21) + (1704707/1000000000000 : ℝ)*(base27) + (49973/500000000000 : ℝ)*(base39) + (282505091851/500000000000 : ℝ)*(base40) + (10352912211/500000000000 : ℝ)*(base50) + (50451387653/200000000000 : ℝ)*(base59) + (11897/6250 : ℝ)*(major_s1_0) + (11897/6250 : ℝ)*(major_s1_1) + (11897/6250 : ℝ)*(major_s1_2) + (1390258039457/500000000000 : ℝ)*(sp_s1_0) + (2780516521119/1000000000000 : ℝ)*(sp_s1_1) + (173782302847/62500000000 : ℝ)*(sp_s1_2) + (62499853943/62500000000 : ℝ)*(sp_s1_6) + (2780516521119/1000000000000 : ℝ)*(f.sum) + (2621124252474421943/4595014895000000000000000000000 : ℝ)*base63 + (16488507302191/174245000000000000000000000 : ℝ)*base65 + (20525039153261/65927500000000000000000000 : ℝ)*base66 + (55266035751099/174245000000000000000000000 : ℝ)*base69 + (10866706194683985081/20808686390000000000000000000000 : ℝ)*base71 + (8232851634271/74638750000000000000000000 : ℝ)*base72 + (42558691/64382324218750000000000 : ℝ)*base74 + (1423440985649/18659687500000000000000000 : ℝ)*base77 + (315217738127035013/492074619062500000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p021_b026 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=47 := by omega
  rcases hc with rfl
  · exact collision_c321047 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p021_b026 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
