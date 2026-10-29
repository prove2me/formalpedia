-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b016
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:36.947423+00:00
-- url     : https://prove2.me/submissions/bd47c3d2-7d70-4e2b-8e72-ac13b1ddff88

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
theorem collision_support_c310028_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6289996549/10000000000 : ℝ)*x 0 + (-1212830469/5000000000 : ℝ)*x 1 + (-3789598853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6289996549/10000000000 : ℝ)^9 ≤ (55096238769623/100000000000000 : ℝ)^7 := by
    have hnat : (6289996549 : ℕ)^9*100000000000000^7 ≤ 55096238769623^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6289996549 10000000000 55096238769623 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1212830469/5000000000 : ℝ)^9 ≤ (16183306685289/100000000000000 : ℝ)^7 := by
    have hnat : (1212830469 : ℕ)^9*100000000000000^7 ≤ 16183306685289^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212830469 5000000000 16183306685289 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3789598853/10000000000 : ℝ)^9 ≤ (28720454539947/100000000000000 : ℝ)^7 := by
    have hnat : (3789598853 : ℕ)^9*100000000000000^7 ≤ 28720454539947^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3789598853 10000000000 28720454539947 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6289996549/10000000000 : ℝ), (-1212830469/5000000000 : ℝ), (-3789598853/10000000000 : ℝ)] ![(55096238769623/100000000000000 : ℝ), (16183306685289/100000000000000 : ℝ), (28720454539947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6289996549/10000000000 : ℝ)|^9 ≤ (55096238769623/100000000000000 : ℝ)^7
        have hw : |(6289996549/10000000000 : ℝ)|=(6289996549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1212830469/5000000000 : ℝ)|^9 ≤ (16183306685289/100000000000000 : ℝ)^7
        have hw : |(-1212830469/5000000000 : ℝ)|=(1212830469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3789598853/10000000000 : ℝ)|^9 ≤ (28720454539947/100000000000000 : ℝ)^7
        have hw : |(-3789598853/10000000000 : ℝ)|=(3789598853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (242566117/1000000000 : ℝ)*x 0 + (1572499089/2500000000 : ℝ)*x 1 + (3789598871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (242566117/1000000000 : ℝ)^9 ≤ (4045827168841/25000000000000 : ℝ)^7 := by
    have hnat : (242566117 : ℕ)^9*25000000000000^7 ≤ 4045827168841^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242566117 1000000000 4045827168841 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1572499089/2500000000 : ℝ)^9 ≤ (11019247319211/20000000000000 : ℝ)^7 := by
    have hnat : (1572499089 : ℕ)^9*20000000000000^7 ≤ 11019247319211^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572499089 2500000000 11019247319211 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3789598871/10000000000 : ℝ)^9 ≤ (14360227357671/50000000000000 : ℝ)^7 := by
    have hnat : (3789598871 : ℕ)^9*50000000000000^7 ≤ 14360227357671^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3789598871 10000000000 14360227357671 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(242566117/1000000000 : ℝ), (1572499089/2500000000 : ℝ), (3789598871/10000000000 : ℝ)] ![(4045827168841/25000000000000 : ℝ), (11019247319211/20000000000000 : ℝ), (14360227357671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(242566117/1000000000 : ℝ)|^9 ≤ (4045827168841/25000000000000 : ℝ)^7
        have hw : |(242566117/1000000000 : ℝ)|=(242566117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1572499089/2500000000 : ℝ)|^9 ≤ (11019247319211/20000000000000 : ℝ)^7
        have hw : |(1572499089/2500000000 : ℝ)|=(1572499089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3789598871/10000000000 : ℝ)|^9 ≤ (14360227357671/50000000000000 : ℝ)^7
        have hw : |(3789598871/10000000000 : ℝ)|=(3789598871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (487111441/1000000000 : ℝ)*x 0 + (2435557119/5000000000 : ℝ)*x 1 + (-2934750351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487111441/1000000000 : ℝ)^9 ≤ (39662426621347/100000000000000 : ℝ)^7 := by
    have hnat : (487111441 : ℕ)^9*100000000000000^7 ≤ 39662426621347^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487111441 1000000000 39662426621347 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2435557119/5000000000 : ℝ)^9 ≤ (39662424820719/100000000000000 : ℝ)^7 := by
    have hnat : (2435557119 : ℕ)^9*100000000000000^7 ≤ 39662424820719^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435557119 5000000000 39662424820719 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2934750351/10000000000 : ℝ)^9 ≤ (4135029708311/20000000000000 : ℝ)^7 := by
    have hnat : (2934750351 : ℕ)^9*20000000000000^7 ≤ 4135029708311^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934750351 10000000000 4135029708311 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(487111441/1000000000 : ℝ), (2435557119/5000000000 : ℝ), (-2934750351/10000000000 : ℝ)] ![(39662426621347/100000000000000 : ℝ), (39662424820719/100000000000000 : ℝ), (4135029708311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(487111441/1000000000 : ℝ)|^9 ≤ (39662426621347/100000000000000 : ℝ)^7
        have hw : |(487111441/1000000000 : ℝ)|=(487111441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2435557119/5000000000 : ℝ)|^9 ≤ (39662424820719/100000000000000 : ℝ)^7
        have hw : |(2435557119/5000000000 : ℝ)|=(2435557119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2934750351/10000000000 : ℝ)|^9 ≤ (4135029708311/20000000000000 : ℝ)^7
        have hw : |(-2934750351/10000000000 : ℝ)|=(2934750351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-740814471/2000000000 : ℝ)*x 0 + (302212959/1000000000 : ℝ)*x 1 + (-5890654747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (740814471/2000000000 : ℝ)^9 ≤ (27889775731109/100000000000000 : ℝ)^7 := by
    have hnat : (740814471 : ℕ)^9*100000000000000^7 ≤ 27889775731109^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740814471 2000000000 27889775731109 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302212959/1000000000 : ℝ)^9 ≤ (5367488412263/25000000000000 : ℝ)^7 := by
    have hnat : (302212959 : ℕ)^9*25000000000000^7 ≤ 5367488412263^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302212959 1000000000 5367488412263 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5890654747/10000000000 : ℝ)^9 ≤ (25320135302471/50000000000000 : ℝ)^7 := by
    have hnat : (5890654747 : ℕ)^9*50000000000000^7 ≤ 25320135302471^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5890654747 10000000000 25320135302471 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-740814471/2000000000 : ℝ), (302212959/1000000000 : ℝ), (-5890654747/10000000000 : ℝ)] ![(27889775731109/100000000000000 : ℝ), (5367488412263/25000000000000 : ℝ), (25320135302471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-740814471/2000000000 : ℝ)|^9 ≤ (27889775731109/100000000000000 : ℝ)^7
        have hw : |(-740814471/2000000000 : ℝ)|=(740814471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(302212959/1000000000 : ℝ)|^9 ≤ (5367488412263/25000000000000 : ℝ)^7
        have hw : |(302212959/1000000000 : ℝ)|=(302212959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5890654747/10000000000 : ℝ)|^9 ≤ (25320135302471/50000000000000 : ℝ)^7
        have hw : |(-5890654747/10000000000 : ℝ)|=(5890654747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (127346461/200000000 : ℝ)*x 0 + (-514785437/2500000000 : ℝ)*x 1 + (-2006812209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127346461/200000000 : ℝ)^9 ≤ (11193723153429/20000000000000 : ℝ)^7 := by
    have hnat : (127346461 : ℕ)^9*20000000000000^7 ≤ 11193723153429^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127346461 200000000 11193723153429 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514785437/2500000000 : ℝ)^9 ≤ (6554908043149/50000000000000 : ℝ)^7 := by
    have hnat : (514785437 : ℕ)^9*50000000000000^7 ≤ 6554908043149^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514785437 2500000000 6554908043149 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006812209/5000000000 : ℝ)^9 ≤ (966299004031/3125000000000 : ℝ)^7 := by
    have hnat : (2006812209 : ℕ)^9*3125000000000^7 ≤ 966299004031^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006812209 5000000000 966299004031 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(127346461/200000000 : ℝ), (-514785437/2500000000 : ℝ), (-2006812209/5000000000 : ℝ)] ![(11193723153429/20000000000000 : ℝ), (6554908043149/50000000000000 : ℝ), (966299004031/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(127346461/200000000 : ℝ)|^9 ≤ (11193723153429/20000000000000 : ℝ)^7
        have hw : |(127346461/200000000 : ℝ)|=(127346461/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514785437/2500000000 : ℝ)|^9 ≤ (6554908043149/50000000000000 : ℝ)^7
        have hw : |(-514785437/2500000000 : ℝ)|=(514785437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2006812209/5000000000 : ℝ)|^9 ≤ (966299004031/3125000000000 : ℝ)^7
        have hw : |(-2006812209/5000000000 : ℝ)|=(2006812209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2107884909/10000000000 : ℝ)*x 0 + (689134201/1000000000 : ℝ)*x 1 + (3352208341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107884909/10000000000 : ℝ)^9 ≤ (3377538449981/25000000000000 : ℝ)^7 := by
    have hnat : (2107884909 : ℕ)^9*25000000000000^7 ≤ 3377538449981^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107884909 10000000000 3377538449981 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689134201/1000000000 : ℝ)^9 ≤ (61959070067487/100000000000000 : ℝ)^7 := by
    have hnat : (689134201 : ℕ)^9*100000000000000^7 ≤ 61959070067487^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689134201 1000000000 61959070067487 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3352208341/10000000000 : ℝ)^9 ≤ (12265388055669/50000000000000 : ℝ)^7 := by
    have hnat : (3352208341 : ℕ)^9*50000000000000^7 ≤ 12265388055669^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3352208341 10000000000 12265388055669 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2107884909/10000000000 : ℝ), (689134201/1000000000 : ℝ), (3352208341/10000000000 : ℝ)] ![(3377538449981/25000000000000 : ℝ), (61959070067487/100000000000000 : ℝ), (12265388055669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2107884909/10000000000 : ℝ)|^9 ≤ (3377538449981/25000000000000 : ℝ)^7
        have hw : |(2107884909/10000000000 : ℝ)|=(2107884909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(689134201/1000000000 : ℝ)|^9 ≤ (61959070067487/100000000000000 : ℝ)^7
        have hw : |(689134201/1000000000 : ℝ)|=(689134201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3352208341/10000000000 : ℝ)|^9 ≤ (12265388055669/50000000000000 : ℝ)^7
        have hw : |(3352208341/10000000000 : ℝ)|=(3352208341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_12 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (862683111/2000000000 : ℝ)*x 0 + (55895127/100000000 : ℝ)*x 1 + (-2718949527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862683111/2000000000 : ℝ)^9 ≤ (4240280061493/12500000000000 : ℝ)^7 := by
    have hnat : (862683111 : ℕ)^9*12500000000000^7 ≤ 4240280061493^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862683111 2000000000 4240280061493 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55895127/100000000 : ℝ)^9 ≤ (47336383530923/100000000000000 : ℝ)^7 := by
    have hnat : (55895127 : ℕ)^9*100000000000000^7 ≤ 47336383530923^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55895127 100000000 47336383530923 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718949527/10000000000 : ℝ)^9 ≤ (585667998913/3125000000000 : ℝ)^7 := by
    have hnat : (2718949527 : ℕ)^9*3125000000000^7 ≤ 585667998913^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718949527 10000000000 585667998913 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862683111/2000000000 : ℝ), (55895127/100000000 : ℝ), (-2718949527/10000000000 : ℝ)] ![(4240280061493/12500000000000 : ℝ), (47336383530923/100000000000000 : ℝ), (585667998913/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862683111/2000000000 : ℝ)|^9 ≤ (4240280061493/12500000000000 : ℝ)^7
        have hw : |(862683111/2000000000 : ℝ)|=(862683111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55895127/100000000 : ℝ)|^9 ≤ (47336383530923/100000000000000 : ℝ)^7
        have hw : |(55895127/100000000 : ℝ)|=(55895127/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2718949527/10000000000 : ℝ)|^9 ≤ (585667998913/3125000000000 : ℝ)^7
        have hw : |(-2718949527/10000000000 : ℝ)|=(2718949527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3848901557/10000000000 : ℝ)*x 0 + (366132549/1000000000 : ℝ)*x 1 + (-5208026159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3848901557/10000000000 : ℝ)^9 ≤ (5859918824743/20000000000000 : ℝ)^7 := by
    have hnat : (3848901557 : ℕ)^9*20000000000000^7 ≤ 5859918824743^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3848901557 10000000000 5859918824743 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366132549/1000000000 : ℝ)^9 ≤ (429322455799/1562500000000 : ℝ)^7 := by
    have hnat : (366132549 : ℕ)^9*1562500000000^7 ≤ 429322455799^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366132549 1000000000 429322455799 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5208026159/10000000000 : ℝ)^9 ≤ (10805942170867/25000000000000 : ℝ)^7 := by
    have hnat : (5208026159 : ℕ)^9*25000000000000^7 ≤ 10805942170867^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208026159 10000000000 10805942170867 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3848901557/10000000000 : ℝ), (366132549/1000000000 : ℝ), (-5208026159/10000000000 : ℝ)] ![(5859918824743/20000000000000 : ℝ), (429322455799/1562500000000 : ℝ), (10805942170867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3848901557/10000000000 : ℝ)|^9 ≤ (5859918824743/20000000000000 : ℝ)^7
        have hw : |(-3848901557/10000000000 : ℝ)|=(3848901557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(366132549/1000000000 : ℝ)|^9 ≤ (429322455799/1562500000000 : ℝ)^7
        have hw : |(366132549/1000000000 : ℝ)|=(366132549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5208026159/10000000000 : ℝ)|^9 ≤ (10805942170867/25000000000000 : ℝ)^7
        have hw : |(-5208026159/10000000000 : ℝ)|=(5208026159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3167893687/5000000000 : ℝ)*x 0 + (-2294583581/10000000000 : ℝ)*x 1 + (-3850965697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3167893687/5000000000 : ℝ)^9 ≤ (11122494203619/20000000000000 : ℝ)^7 := by
    have hnat : (3167893687 : ℕ)^9*20000000000000^7 ≤ 11122494203619^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167893687 5000000000 11122494203619 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2294583581/10000000000 : ℝ)^9 ≤ (15067730638053/100000000000000 : ℝ)^7 := by
    have hnat : (2294583581 : ℕ)^9*100000000000000^7 ≤ 15067730638053^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294583581 10000000000 15067730638053 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3850965697/10000000000 : ℝ)^9 ≤ (5863959665009/20000000000000 : ℝ)^7 := by
    have hnat : (3850965697 : ℕ)^9*20000000000000^7 ≤ 5863959665009^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3850965697 10000000000 5863959665009 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3167893687/5000000000 : ℝ), (-2294583581/10000000000 : ℝ), (-3850965697/10000000000 : ℝ)] ![(11122494203619/20000000000000 : ℝ), (15067730638053/100000000000000 : ℝ), (5863959665009/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3167893687/5000000000 : ℝ)|^9 ≤ (11122494203619/20000000000000 : ℝ)^7
        have hw : |(3167893687/5000000000 : ℝ)|=(3167893687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2294583581/10000000000 : ℝ)|^9 ≤ (15067730638053/100000000000000 : ℝ)^7
        have hw : |(-2294583581/10000000000 : ℝ)|=(2294583581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3850965697/10000000000 : ℝ)|^9 ≤ (5863959665009/20000000000000 : ℝ)^7
        have hw : |(-3850965697/10000000000 : ℝ)|=(3850965697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2145090759/10000000000 : ℝ)*x 0 + (3096382277/5000000000 : ℝ)*x 1 + (4139989059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145090759/10000000000 : ℝ)^9 ≤ (345438038007/2500000000000 : ℝ)^7 := by
    have hnat : (2145090759 : ℕ)^9*2500000000000^7 ≤ 345438038007^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145090759 10000000000 345438038007 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3096382277/5000000000 : ℝ)^9 ≤ (27001818963923/50000000000000 : ℝ)^7 := by
    have hnat : (3096382277 : ℕ)^9*50000000000000^7 ≤ 27001818963923^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3096382277 5000000000 27001818963923 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4139989059/10000000000 : ℝ)^9 ≤ (3217884052833/10000000000000 : ℝ)^7 := by
    have hnat : (4139989059 : ℕ)^9*10000000000000^7 ≤ 3217884052833^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139989059 10000000000 3217884052833 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145090759/10000000000 : ℝ), (3096382277/5000000000 : ℝ), (4139989059/10000000000 : ℝ)] ![(345438038007/2500000000000 : ℝ), (27001818963923/50000000000000 : ℝ), (3217884052833/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145090759/10000000000 : ℝ)|^9 ≤ (345438038007/2500000000000 : ℝ)^7
        have hw : |(2145090759/10000000000 : ℝ)|=(2145090759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3096382277/5000000000 : ℝ)|^9 ≤ (27001818963923/50000000000000 : ℝ)^7
        have hw : |(3096382277/5000000000 : ℝ)|=(3096382277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4139989059/10000000000 : ℝ)|^9 ≤ (3217884052833/10000000000000 : ℝ)^7
        have hw : |(4139989059/10000000000 : ℝ)|=(4139989059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4790939193/10000000000 : ℝ)*x 0 + (78524259/156250000 : ℝ)*x 1 + (-2847524667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4790939193/10000000000 : ℝ)^9 ≤ (38825072518567/100000000000000 : ℝ)^7 := by
    have hnat : (4790939193 : ℕ)^9*100000000000000^7 ≤ 38825072518567^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790939193 10000000000 38825072518567 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78524259/156250000 : ℝ)^9 ≤ (8257294331127/20000000000000 : ℝ)^7 := by
    have hnat : (78524259 : ℕ)^9*20000000000000^7 ≤ 8257294331127^7*156250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78524259 156250000 8257294331127 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2847524667/10000000000 : ℝ)^9 ≤ (3977691163367/20000000000000 : ℝ)^7 := by
    have hnat : (2847524667 : ℕ)^9*20000000000000^7 ≤ 3977691163367^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847524667 10000000000 3977691163367 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4790939193/10000000000 : ℝ), (78524259/156250000 : ℝ), (-2847524667/10000000000 : ℝ)] ![(38825072518567/100000000000000 : ℝ), (8257294331127/20000000000000 : ℝ), (3977691163367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4790939193/10000000000 : ℝ)|^9 ≤ (38825072518567/100000000000000 : ℝ)^7
        have hw : |(4790939193/10000000000 : ℝ)|=(4790939193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78524259/156250000 : ℝ)|^9 ≤ (8257294331127/20000000000000 : ℝ)^7
        have hw : |(78524259/156250000 : ℝ)|=(78524259/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2847524667/10000000000 : ℝ)|^9 ≤ (3977691163367/20000000000000 : ℝ)^7
        have hw : |(-2847524667/10000000000 : ℝ)|=(2847524667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3037430107/10000000000 : ℝ)*x 0 + (3824174953/10000000000 : ℝ)*x 1 + (-180374437/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3037430107/10000000000 : ℝ)^9 ≤ (5402452501881/25000000000000 : ℝ)^7 := by
    have hnat : (3037430107 : ℕ)^9*25000000000000^7 ≤ 5402452501881^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3037430107 10000000000 5402452501881 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3824174953/10000000000 : ℝ)^9 ≤ (29057806331057/100000000000000 : ℝ)^7 := by
    have hnat : (3824174953 : ℕ)^9*100000000000000^7 ≤ 29057806331057^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3824174953 10000000000 29057806331057 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180374437/312500000 : ℝ)^9 ≤ (49332383647497/100000000000000 : ℝ)^7 := by
    have hnat : (180374437 : ℕ)^9*100000000000000^7 ≤ 49332383647497^7*312500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180374437 312500000 49332383647497 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3037430107/10000000000 : ℝ), (3824174953/10000000000 : ℝ), (-180374437/312500000 : ℝ)] ![(5402452501881/25000000000000 : ℝ), (29057806331057/100000000000000 : ℝ), (49332383647497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3037430107/10000000000 : ℝ)|^9 ≤ (5402452501881/25000000000000 : ℝ)^7
        have hw : |(-3037430107/10000000000 : ℝ)|=(3037430107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3824174953/10000000000 : ℝ)|^9 ≤ (29057806331057/100000000000000 : ℝ)^7
        have hw : |(3824174953/10000000000 : ℝ)|=(3824174953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-180374437/312500000 : ℝ)|^9 ≤ (49332383647497/100000000000000 : ℝ)^7
        have hw : |(-180374437/312500000 : ℝ)|=(180374437/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3454817827/5000000000 : ℝ)*x 0 + (-2169819471/10000000000 : ℝ)*x 1 + (-3274996319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3454817827/5000000000 : ℝ)^9 ≤ (31085309378739/50000000000000 : ℝ)^7 := by
    have hnat : (3454817827 : ℕ)^9*50000000000000^7 ≤ 31085309378739^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3454817827 5000000000 31085309378739 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2169819471/10000000000 : ℝ)^9 ≤ (2804531621799/20000000000000 : ℝ)^7 := by
    have hnat : (2169819471 : ℕ)^9*20000000000000^7 ≤ 2804531621799^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169819471 10000000000 2804531621799 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3274996319/10000000000 : ℝ)^9 ≤ (11903361555383/50000000000000 : ℝ)^7 := by
    have hnat : (3274996319 : ℕ)^9*50000000000000^7 ≤ 11903361555383^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3274996319 10000000000 11903361555383 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3454817827/5000000000 : ℝ), (-2169819471/10000000000 : ℝ), (-3274996319/10000000000 : ℝ)] ![(31085309378739/50000000000000 : ℝ), (2804531621799/20000000000000 : ℝ), (11903361555383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3454817827/5000000000 : ℝ)|^9 ≤ (31085309378739/50000000000000 : ℝ)^7
        have hw : |(3454817827/5000000000 : ℝ)|=(3454817827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2169819471/10000000000 : ℝ)|^9 ≤ (2804531621799/20000000000000 : ℝ)^7
        have hw : |(-2169819471/10000000000 : ℝ)|=(2169819471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3274996319/10000000000 : ℝ)|^9 ≤ (11903361555383/50000000000000 : ℝ)^7
        have hw : |(-3274996319/10000000000 : ℝ)|=(3274996319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1019702641/5000000000 : ℝ)*x 0 + (3250850091/5000000000 : ℝ)*x 1 + (387545067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019702641/5000000000 : ℝ)^9 ≤ (1618560173439/12500000000000 : ℝ)^7 := by
    have hnat : (1019702641 : ℕ)^9*12500000000000^7 ≤ 1618560173439^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019702641 5000000000 1618560173439 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3250850091/5000000000 : ℝ)^9 ≤ (2874591045057/5000000000000 : ℝ)^7 := by
    have hnat : (3250850091 : ℕ)^9*5000000000000^7 ≤ 2874591045057^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3250850091 5000000000 2874591045057 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387545067/1000000000 : ℝ)^9 ≤ (5911939541/20000000000 : ℝ)^7 := by
    have hnat : (387545067 : ℕ)^9*20000000000^7 ≤ 5911939541^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387545067 1000000000 5911939541 20000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1019702641/5000000000 : ℝ), (3250850091/5000000000 : ℝ), (387545067/1000000000 : ℝ)] ![(1618560173439/12500000000000 : ℝ), (2874591045057/5000000000000 : ℝ), (5911939541/20000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1019702641/5000000000 : ℝ)|^9 ≤ (1618560173439/12500000000000 : ℝ)^7
        have hw : |(1019702641/5000000000 : ℝ)|=(1019702641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3250850091/5000000000 : ℝ)|^9 ≤ (2874591045057/5000000000000 : ℝ)^7
        have hw : |(3250850091/5000000000 : ℝ)|=(3250850091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(387545067/1000000000 : ℝ)|^9 ≤ (5911939541/20000000000 : ℝ)^7
        have hw : |(387545067/1000000000 : ℝ)|=(387545067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s0_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5558527149/10000000000 : ℝ)*x 0 + (4419978179/10000000000 : ℝ)*x 1 + (-2634604321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5558527149/10000000000 : ℝ)^9 ≤ (11749816701763/25000000000000 : ℝ)^7 := by
    have hnat : (5558527149 : ℕ)^9*25000000000000^7 ≤ 11749816701763^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5558527149 10000000000 11749816701763 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4419978179/10000000000 : ℝ)^9 ≤ (7000701902529/20000000000000 : ℝ)^7 := by
    have hnat : (4419978179 : ℕ)^9*20000000000000^7 ≤ 7000701902529^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419978179 10000000000 7000701902529 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2634604321/10000000000 : ℝ)^9 ≤ (8998611832487/50000000000000 : ℝ)^7 := by
    have hnat : (2634604321 : ℕ)^9*50000000000000^7 ≤ 8998611832487^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2634604321 10000000000 8998611832487 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5558527149/10000000000 : ℝ), (4419978179/10000000000 : ℝ), (-2634604321/10000000000 : ℝ)] ![(11749816701763/25000000000000 : ℝ), (7000701902529/20000000000000 : ℝ), (8998611832487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5558527149/10000000000 : ℝ)|^9 ≤ (11749816701763/25000000000000 : ℝ)^7
        have hw : |(5558527149/10000000000 : ℝ)|=(5558527149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4419978179/10000000000 : ℝ)|^9 ≤ (7000701902529/20000000000000 : ℝ)^7
        have hw : |(4419978179/10000000000 : ℝ)|=(4419978179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2634604321/10000000000 : ℝ)|^9 ≤ (8998611832487/50000000000000 : ℝ)^7
        have hw : |(-2634604321/10000000000 : ℝ)|=(2634604321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-494733243/1250000000 : ℝ)*x 0 + (3958205323/10000000000 : ℝ)*x 1 + (-4832240421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (494733243/1250000000 : ℝ)^9 ≤ (30370361424013/100000000000000 : ℝ)^7 := by
    have hnat : (494733243 : ℕ)^9*100000000000000^7 ≤ 30370361424013^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494733243 1250000000 30370361424013 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3958205323/10000000000 : ℝ)^9 ≤ (15186854859201/50000000000000 : ℝ)^7 := by
    have hnat : (3958205323 : ℕ)^9*50000000000000^7 ≤ 15186854859201^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3958205323 10000000000 15186854859201 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4832240421/10000000000 : ℝ)^9 ≤ (19627964422949/50000000000000 : ℝ)^7 := by
    have hnat : (4832240421 : ℕ)^9*50000000000000^7 ≤ 19627964422949^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4832240421 10000000000 19627964422949 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-494733243/1250000000 : ℝ), (3958205323/10000000000 : ℝ), (-4832240421/10000000000 : ℝ)] ![(30370361424013/100000000000000 : ℝ), (15186854859201/50000000000000 : ℝ), (19627964422949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-494733243/1250000000 : ℝ)|^9 ≤ (30370361424013/100000000000000 : ℝ)^7
        have hw : |(-494733243/1250000000 : ℝ)|=(494733243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3958205323/10000000000 : ℝ)|^9 ≤ (15186854859201/50000000000000 : ℝ)^7
        have hw : |(3958205323/10000000000 : ℝ)|=(3958205323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4832240421/10000000000 : ℝ)|^9 ≤ (19627964422949/50000000000000 : ℝ)^7
        have hw : |(-4832240421/10000000000 : ℝ)|=(4832240421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2626837119/5000000000 : ℝ)*x 0 + (-134187373/400000000 : ℝ)*x 1 + (-2047726163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626837119/5000000000 : ℝ)^9 ≤ (21855737721519/50000000000000 : ℝ)^7 := by
    have hnat : (2626837119 : ℕ)^9*50000000000000^7 ≤ 21855737721519^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626837119 5000000000 21855737721519 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134187373/400000000 : ℝ)^9 ≤ (4910814819729/20000000000000 : ℝ)^7 := by
    have hnat : (134187373 : ℕ)^9*20000000000000^7 ≤ 4910814819729^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134187373 400000000 4910814819729 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2047726163/5000000000 : ℝ)^9 ≤ (1586722522167/5000000000000 : ℝ)^7 := by
    have hnat : (2047726163 : ℕ)^9*5000000000000^7 ≤ 1586722522167^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047726163 5000000000 1586722522167 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626837119/5000000000 : ℝ), (-134187373/400000000 : ℝ), (-2047726163/5000000000 : ℝ)] ![(21855737721519/50000000000000 : ℝ), (4910814819729/20000000000000 : ℝ), (1586722522167/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626837119/5000000000 : ℝ)|^9 ≤ (21855737721519/50000000000000 : ℝ)^7
        have hw : |(2626837119/5000000000 : ℝ)|=(2626837119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134187373/400000000 : ℝ)|^9 ≤ (4910814819729/20000000000000 : ℝ)^7
        have hw : |(-134187373/400000000 : ℝ)|=(134187373/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2047726163/5000000000 : ℝ)|^9 ≤ (1586722522167/5000000000000 : ℝ)^7
        have hw : |(-2047726163/5000000000 : ℝ)|=(2047726163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3354617883/10000000000 : ℝ)*x 0 + (5253481177/10000000000 : ℝ)*x 1 + (2047861191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3354617883/10000000000 : ℝ)^9 ≤ (4910689768537/20000000000000 : ℝ)^7 := by
    have hnat : (3354617883 : ℕ)^9*20000000000000^7 ≤ 4910689768537^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3354617883 10000000000 4910689768537 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253481177/10000000000 : ℝ)^9 ≤ (43709410209987/100000000000000 : ℝ)^7 := by
    have hnat : (5253481177 : ℕ)^9*100000000000000^7 ≤ 43709410209987^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253481177 10000000000 43709410209987 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2047861191/5000000000 : ℝ)^9 ≤ (15868570467029/50000000000000 : ℝ)^7 := by
    have hnat : (2047861191 : ℕ)^9*50000000000000^7 ≤ 15868570467029^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047861191 5000000000 15868570467029 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3354617883/10000000000 : ℝ), (5253481177/10000000000 : ℝ), (2047861191/5000000000 : ℝ)] ![(4910689768537/20000000000000 : ℝ), (43709410209987/100000000000000 : ℝ), (15868570467029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3354617883/10000000000 : ℝ)|^9 ≤ (4910689768537/20000000000000 : ℝ)^7
        have hw : |(3354617883/10000000000 : ℝ)|=(3354617883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253481177/10000000000 : ℝ)|^9 ≤ (43709410209987/100000000000000 : ℝ)^7
        have hw : |(5253481177/10000000000 : ℝ)|=(5253481177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2047861191/5000000000 : ℝ)|^9 ≤ (15868570467029/50000000000000 : ℝ)^7
        have hw : |(2047861191/5000000000 : ℝ)|=(2047861191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310028_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2292156483/5000000000 : ℝ)*x 0 + (4583842243/10000000000 : ℝ)*x 1 + (-893414511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2292156483/5000000000 : ℝ)^9 ≤ (36685587256019/100000000000000 : ℝ)^7 := by
    have hnat : (2292156483 : ℕ)^9*100000000000000^7 ≤ 36685587256019^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292156483 5000000000 36685587256019 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4583842243/10000000000 : ℝ)^9 ≤ (7336148828309/20000000000000 : ℝ)^7 := by
    have hnat : (4583842243 : ℕ)^9*20000000000000^7 ≤ 7336148828309^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4583842243 10000000000 7336148828309 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893414511/2500000000 : ℝ)^9 ≤ (5326733719593/20000000000000 : ℝ)^7 := by
    have hnat : (893414511 : ℕ)^9*20000000000000^7 ≤ 5326733719593^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893414511 2500000000 5326733719593 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2292156483/5000000000 : ℝ), (4583842243/10000000000 : ℝ), (-893414511/2500000000 : ℝ)] ![(36685587256019/100000000000000 : ℝ), (7336148828309/20000000000000 : ℝ), (5326733719593/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2292156483/5000000000 : ℝ)|^9 ≤ (36685587256019/100000000000000 : ℝ)^7
        have hw : |(2292156483/5000000000 : ℝ)|=(2292156483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4583842243/10000000000 : ℝ)|^9 ≤ (7336148828309/20000000000000 : ℝ)^7
        have hw : |(4583842243/10000000000 : ℝ)|=(4583842243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-893414511/2500000000 : ℝ)|^9 ≤ (5326733719593/20000000000000 : ℝ)^7
        have hw : |(-893414511/2500000000 : ℝ)|=(893414511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310028 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((6289996549/10000000000 : ℝ)*X 1 0+(-1212830469/5000000000 : ℝ)*X 1 1+(-3789598853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((242566117/1000000000 : ℝ)*X 2 0+(1572499089/2500000000 : ℝ)*X 2 1+(3789598871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((487111441/1000000000 : ℝ)*X 0 0+(2435557119/5000000000 : ℝ)*X 0 1+(-2934750351/10000000000 : ℝ)*X 0 2+(487111441/1000000000 : ℝ)*X 1 0+(2435557119/5000000000 : ℝ)*X 1 1+(-2934750351/10000000000 : ℝ)*X 1 2+(487111441/1000000000 : ℝ)*X 2 0+(2435557119/5000000000 : ℝ)*X 2 1+(-2934750351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-740814471/2000000000 : ℝ)*X 0 0+(302212959/1000000000 : ℝ)*X 0 1+(-5890654747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((127346461/200000000 : ℝ)*X 1 0+(-514785437/2500000000 : ℝ)*X 1 1+(-2006812209/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2107884909/10000000000 : ℝ)*X 2 0+(689134201/1000000000 : ℝ)*X 2 1+(3352208341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((862683111/2000000000 : ℝ)*X 0 0+(55895127/100000000 : ℝ)*X 0 1+(-2718949527/10000000000 : ℝ)*X 0 2+(862683111/2000000000 : ℝ)*X 1 0+(55895127/100000000 : ℝ)*X 1 1+(-2718949527/10000000000 : ℝ)*X 1 2+(862683111/2000000000 : ℝ)*X 2 0+(55895127/100000000 : ℝ)*X 2 1+(-2718949527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-3848901557/10000000000 : ℝ)*X 0 0+(366132549/1000000000 : ℝ)*X 0 1+(-5208026159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((3167893687/5000000000 : ℝ)*X 1 0+(-2294583581/10000000000 : ℝ)*X 1 1+(-3850965697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2145090759/10000000000 : ℝ)*X 2 0+(3096382277/5000000000 : ℝ)*X 2 1+(4139989059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((4790939193/10000000000 : ℝ)*X 0 0+(78524259/156250000 : ℝ)*X 0 1+(-2847524667/10000000000 : ℝ)*X 0 2+(4790939193/10000000000 : ℝ)*X 1 0+(78524259/156250000 : ℝ)*X 1 1+(-2847524667/10000000000 : ℝ)*X 1 2+(4790939193/10000000000 : ℝ)*X 2 0+(78524259/156250000 : ℝ)*X 2 1+(-2847524667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-3037430107/10000000000 : ℝ)*X 0 0+(3824174953/10000000000 : ℝ)*X 0 1+(-180374437/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((3454817827/5000000000 : ℝ)*X 1 0+(-2169819471/10000000000 : ℝ)*X 1 1+(-3274996319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1019702641/5000000000 : ℝ)*X 2 0+(3250850091/5000000000 : ℝ)*X 2 1+(387545067/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((5558527149/10000000000 : ℝ)*X 0 0+(4419978179/10000000000 : ℝ)*X 0 1+(-2634604321/10000000000 : ℝ)*X 0 2+(5558527149/10000000000 : ℝ)*X 1 0+(4419978179/10000000000 : ℝ)*X 1 1+(-2634604321/10000000000 : ℝ)*X 1 2+(5558527149/10000000000 : ℝ)*X 2 0+(4419978179/10000000000 : ℝ)*X 2 1+(-2634604321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((3989/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3989/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11188313392527076022529/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (324104085479/250000000000 : ℝ)*(base39) + (1184483742153/1000000000000 : ℝ)*(base49) + (1944610346727/1000000000000 : ℝ)*(base50) + (976067836753/1000000000000 : ℝ)*(base59) + (3964153434697/500000000000 : ℝ)*(major_s0_0) + (3964153434697/500000000000 : ℝ)*(major_s0_1) + (3964153434697/500000000000 : ℝ)*(major_s0_2) + (69716801/250000000000 : ℝ)*(sp_s0_1) + (10956317651151/1000000000000 : ℝ)*(sp_s0_7) + (10956053835583/1000000000000 : ℝ)*(sp_s0_8) + (5478065663299/500000000000 : ℝ)*(sp_s0_9) + (2450139026223/500000000000 : ℝ)*(sp_s0_12) + (15051637/1000000000000 : ℝ)*(sp_s0_20) + (201376189/1000000000000 : ℝ)*(sp_s0_22) + (2450139026223/500000000000 : ℝ)*(f.failure) + (10956332702787/1000000000000 : ℝ)*(f.sum) + (3327134117/5000000000000000000000 : ℝ)*base63 + (767998916540423/5000000000000000000000000000 : ℝ)*base64 + (7027996064540423/5000000000000000000000000000 : ℝ)*base67 + (1396090031777891/5000000000000000000000000000 : ℝ)*base68 + (1189097341590843/2500000000000000000000000000 : ℝ)*base71 + (581048384959577/5000000000000000000000000000 : ℝ)*base72 + (251138988777891/5000000000000000000000000000 : ℝ)*base75 + (1228613982777891/5000000000000000000000000000 : ℝ)*base76 + (385624364540423/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (2161/50000000000000000 : ℝ)*base86 + (2161/50000000000000000 : ℝ)*base88 + (2161/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2327/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2327/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (493180599365302492407/31250000000000000000000000 : ℝ) := by norm_num
    linear_combination (15736391579/20000000000 : ℝ)*(base39) + (10482642847/250000000000 : ℝ)*(base50) + (284477734317/1000000000000 : ℝ)*(base59) + (276200516027/62500000000 : ℝ)*(major_s0_0) + (276200516027/62500000000 : ℝ)*(major_s0_1) + (276200516027/62500000000 : ℝ)*(major_s0_2) + (104722783/100000000000 : ℝ)*(sp_s0_1) + (77746909/500000000000 : ℝ)*(sp_s0_2) + (483609521/1000000000000 : ℝ)*(sp_s0_6) + (464445741/500000000000 : ℝ)*(sp_s0_8) + (1526753700863/250000000000 : ℝ)*(sp_s0_13) + (305251934207/50000000000 : ℝ)*(sp_s0_14) + (3053429654817/500000000000 : ℝ)*(sp_s0_15) + (546182567859/200000000000 : ℝ)*(sp_s0_19) + (170712278051/62500000000 : ℝ)*(f.failure) + (1526753700863/250000000000 : ℝ)*(f.sum) + (3430511781/10000000000000000000000 : ℝ)*base62 + (133830785150893/625000000000000000000000000 : ℝ)*base64 + (89846854275893/625000000000000000000000000 : ℝ)*base67 + (166788446791381/625000000000000000000000000 : ℝ)*base68 + (66736316877387/312500000000000000000000000 : ℝ)*base70 + (97567552900893/625000000000000000000000000 : ℝ)*base73 + (212296521083619/625000000000000000000000000 : ℝ)*base74 + (173714739728881/625000000000000000000000000 : ℝ)*base76 + (35670065025893/312500000000000000000000000 : ℝ)*base79 + (5443/6250000000000000 : ℝ)*base87 + (5443/6250000000000000 : ℝ)*base89 + (5443/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-20269/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-20269/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3892643208960313295583/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1933927401557/1000000000000 : ℝ)*(base39) + (812539462557/1000000000000 : ℝ)*(base49) + (1601154260781/1000000000000 : ℝ)*(base50) + (333591702127/500000000000 : ℝ)*(base59) + (986244569281/125000000000 : ℝ)*(major_s0_0) + (986244569281/125000000000 : ℝ)*(major_s0_1) + (986244569281/125000000000 : ℝ)*(major_s0_2) + (91845617/1000000000000 : ℝ)*(sp_s0_1) + (263663719/1000000000000 : ℝ)*(sp_s0_2) + (19206883/100000000000 : ℝ)*(sp_s0_9) + (10903334225507/1000000000000 : ℝ)*(sp_s0_20) + (1090324237989/100000000000 : ℝ)*(sp_s0_21) + (5451439246479/500000000000 : ℝ)*(sp_s0_22) + (4876574730827/1000000000000 : ℝ)*(sp_s0_25) + (4876574730827/1000000000000 : ℝ)*(f.failure) + (10903334225507/1000000000000 : ℝ)*(f.sum) + (378791487/5000000000000000000000 : ℝ)*base62 + (1015430890241521/1250000000000000000000000000 : ℝ)*base65 + (570228496366521/1250000000000000000000000000 : ℝ)*base66 + (898321172144757/1250000000000000000000000000 : ℝ)*base69 + (311967851380639/625000000000000000000000000 : ℝ)*base71 + (271648955991521/1250000000000000000000000000 : ℝ)*base72 + (310653815980243/1250000000000000000000000000 : ℝ)*base75 + (799720842519757/1250000000000000000000000000 : ℝ)*base77 + (135384667258479/625000000000000000000000000 : ℝ)*base79 + (107189/100000000000000000 : ℝ)*base86 + (107189/100000000000000000 : ℝ)*base88 + (107189/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (3989/20000 : ℝ) ^ (35/8 : ℝ) ≤ (86451777653449147/100000000000000000000 : ℝ) := by
    have hpowers : (3989/20000 : ℝ)^35 ≤ (86451777653449147/100000000000000000000 : ℝ)^8 := by
      have hnat : (3989 : ℕ)^35*100000000000000000000^8 ≤ 86451777653449147^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3989 20000 86451777653449147 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3989/20000 : ℝ)) (X := (86451777653449147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100086451777653449147/100000000000000000000 : ℝ) ≤ (5000987691021973/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100086451777653449147/100000000000000000000 : ℝ)^8 ≤ (5000987691021973/5000000000000000 : ℝ)^35 := by
      have hnat : (100086451777653449147 : ℕ)^8*5000000000000000^35 ≤ 5000987691021973^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100086451777653449147 100000000000000000000 5000987691021973 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000987691021973/5000000000000000 : ℝ)) (X := (100086451777653449147/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50086451777653449147/50000000000000000000 : ℝ) ≤ (5001974724127337/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50086451777653449147/50000000000000000000 : ℝ)^8 ≤ (5001974724127337/5000000000000000 : ℝ)^35 := by
      have hnat : (50086451777653449147 : ℕ)^8*5000000000000000^35 ≤ 5001974724127337^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50086451777653449147 50000000000000000000 5001974724127337 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001974724127337/5000000000000000 : ℝ)) (X := (50086451777653449147/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(987691021973/997250000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(246758276341/249312500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (3989/20000 : ℝ)) (alpha := (987691021973/997250000000000 : ℝ)) (beta := (246758276341/249312500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3989/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(987691021973/997250000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(246758276341/249312500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2327/100000 : ℝ) ^ (35/8 : ℝ) ≤ (3578526035109/50000000000000000000 : ℝ) := by
    have hpowers : (2327/100000 : ℝ)^35 ≤ (3578526035109/50000000000000000000 : ℝ)^8 := by
      have hnat : (2327 : ℕ)^35*50000000000000000000^8 ≤ 3578526035109^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2327 100000 3578526035109 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2327/100000 : ℝ)) (X := (3578526035109/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50000003578526035109/50000000000000000000 : ℝ) ≤ (5000000081794879/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50000003578526035109/50000000000000000000 : ℝ)^8 ≤ (5000000081794879/5000000000000000 : ℝ)^35 := by
      have hnat : (50000003578526035109 : ℕ)^8*5000000000000000^35 ≤ 5000000081794879^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000003578526035109 50000000000000000000 5000000081794879 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000081794879/5000000000000000 : ℝ)) (X := (50000003578526035109/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25000003578526035109/25000000000000000000 : ℝ) ≤ (5000000163589753/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25000003578526035109/25000000000000000000 : ℝ)^8 ≤ (5000000163589753/5000000000000000 : ℝ)^35 := by
      have hnat : (25000003578526035109 : ℕ)^8*5000000000000000^35 ≤ 5000000163589753^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000003578526035109 25000000000000000000 5000000163589753 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000163589753/5000000000000000 : ℝ)) (X := (25000003578526035109/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(81794879/116350000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(40897437/58175000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (2327/100000 : ℝ)) (alpha := (81794879/116350000000000 : ℝ)) (beta := (40897437/58175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (2327/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(81794879/116350000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(40897437/58175000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (20269/100000 : ℝ) ^ (35/8 : ℝ) ≤ (2898954729648697/3125000000000000000 : ℝ) := by
    have hpowers : (20269/100000 : ℝ)^35 ≤ (2898954729648697/3125000000000000000 : ℝ)^8 := by
      have hnat : (20269 : ℕ)^35*3125000000000000000^8 ≤ 2898954729648697^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20269 100000 2898954729648697 3125000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20269/100000 : ℝ)) (X := (2898954729648697/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (3127898954729648697/3125000000000000000 : ℝ) ≤ (2500529905007789/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3127898954729648697/3125000000000000000 : ℝ)^8 ≤ (2500529905007789/2500000000000000 : ℝ)^35 := by
      have hnat : (3127898954729648697 : ℕ)^8*2500000000000000^35 ≤ 2500529905007789^35*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127898954729648697 3125000000000000000 2500529905007789 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500529905007789/2500000000000000 : ℝ)) (X := (3127898954729648697/3125000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1565398954729648697/1562500000000000000 : ℝ) ≤ (5002118862575347/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (1565398954729648697/1562500000000000000 : ℝ)^8 ≤ (5002118862575347/5000000000000000 : ℝ)^35 := by
      have hnat : (1565398954729648697 : ℕ)^8*5000000000000000^35 ≤ 5002118862575347^35*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1565398954729648697 1562500000000000000 5002118862575347 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002118862575347/5000000000000000 : ℝ)) (X := (1565398954729648697/1562500000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(529905007789/506725000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1059052559769/1013450000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (20269/100000 : ℝ)) (alpha := (529905007789/506725000000000 : ℝ)) (beta := (1059052559769/1013450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (20269/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(529905007789/506725000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1059052559769/1013450000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-494733243/1250000000 : ℝ)*X 0 0+(3958205323/10000000000 : ℝ)*X 0 1+(-4832240421/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2626837119/5000000000 : ℝ)*X 1 0+(-134187373/400000000 : ℝ)*X 1 1+(-2047726163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3354617883/10000000000 : ℝ)*X 2 0+(5253481177/10000000000 : ℝ)*X 2 1+(2047861191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2292156483/5000000000 : ℝ)*X 0 0+(4583842243/10000000000 : ℝ)*X 0 1+(-893414511/2500000000 : ℝ)*X 0 2+(2292156483/5000000000 : ℝ)*X 1 0+(4583842243/10000000000 : ℝ)*X 1 1+(-893414511/2500000000 : ℝ)*X 1 2+(2292156483/5000000000 : ℝ)*X 2 0+(4583842243/10000000000 : ℝ)*X 2 1+(-893414511/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310028_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-3118849673539477444420091692836783/470362566017500000000000000000000 : ℝ) := by norm_num
    linear_combination (30587/500000000000 : ℝ)*(base5) + (7317/15625000000 : ℝ)*(base12) + (176883759371/500000000000 : ℝ)*(base39) + (12211281647/20000000000 : ℝ)*(base49) + (418044816669/1000000000000 : ℝ)*(base50) + (282994947993/1000000000000 : ℝ)*(base59) + (16871/200000000000 : ℝ)*(base60) + (1781/20000000000 : ℝ)*(ratio_s0_0) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (221024463401/100000000000 : ℝ)*(sp_s1_0) + (1105122551149/500000000000 : ℝ)*(sp_s1_1) + (138140322717/62500000000 : ℝ)*(sp_s1_2) + (499999969413/500000000000 : ℝ)*(sp_s1_6) + (1105122551149/500000000000 : ℝ)*(f.sum) + (85789498689773903/117914907500000000000000000000 : ℝ)*base63 + (49633698943997/50672500000000000000000000 : ℝ)*base65 + (1164395446421/11635000000000000000000000 : ℝ)*base66 + (2573438536751/5067250000000000000000000 : ℝ)*base69 + (265687750591133353/202132602500000000000000000000 : ℝ)*base71 + (3496515822897/9972500000000000000000000 : ℝ)*base73 + (220152060179/5817500000000000000000000 : ℝ)*base75 + (4355441538941/19945000000000000000000000 : ℝ)*base77 + (4172007651353/2320600750000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p010_b016 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 28 ≤ c.val) (hhi : c.val < 29)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=28 := by omega
  rcases hc with rfl
  · exact collision_c310028 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 28 ≤ c.val) (hhi : c.val < 29)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b016 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
