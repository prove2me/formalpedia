-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b015
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:16:51.477049+00:00
-- url     : https://prove2.me/submissions/37c544f3-5d9b-407d-958e-ca4b233d8b0e

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
theorem collision_support_c301027_s0_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4552100083/10000000000 : ℝ)*x 0 + (-57330821/400000000 : ℝ)*x 1 + (820334297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4552100083/10000000000 : ℝ)^65 ≤ (35205254838441/100000000000000 : ℝ)^49 := by
    have hnat : (4552100083 : ℕ)^65*100000000000000^49 ≤ 35205254838441^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4552100083 10000000000 35205254838441 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57330821/400000000 : ℝ)^65 ≤ (3800261613121/50000000000000 : ℝ)^49 := by
    have hnat : (57330821 : ℕ)^65*50000000000000^49 ≤ 3800261613121^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57330821 400000000 3800261613121 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (820334297/1250000000 : ℝ)^65 ≤ (11438844383121/20000000000000 : ℝ)^49 := by
    have hnat : (820334297 : ℕ)^65*20000000000000^49 ≤ 11438844383121^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820334297 1250000000 11438844383121 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4552100083/10000000000 : ℝ), (-57330821/400000000 : ℝ), (820334297/1250000000 : ℝ)] ![(35205254838441/100000000000000 : ℝ), (3800261613121/50000000000000 : ℝ), (11438844383121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4552100083/10000000000 : ℝ)|^65 ≤ (35205254838441/100000000000000 : ℝ)^49
        have hw : |(4552100083/10000000000 : ℝ)|=(4552100083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57330821/400000000 : ℝ)|^65 ≤ (3800261613121/50000000000000 : ℝ)^49
        have hw : |(-57330821/400000000 : ℝ)|=(57330821/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(820334297/1250000000 : ℝ)|^65 ≤ (11438844383121/20000000000000 : ℝ)^49
        have hw : |(820334297/1250000000 : ℝ)|=(820334297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4280551/10000000 : ℝ)*x 0 + (6604225419/10000000000 : ℝ)*x 1 + (-873184743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280551/10000000 : ℝ)^65 ≤ (32446887220873/100000000000000 : ℝ)^49 := by
    have hnat : (4280551 : ℕ)^65*100000000000000^49 ≤ 32446887220873^49*10000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280551 10000000 32446887220873 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6604225419/10000000000 : ℝ)^65 ≤ (57675081824069/100000000000000 : ℝ)^49 := by
    have hnat : (6604225419 : ℕ)^65*100000000000000^49 ≤ 57675081824069^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6604225419 10000000000 57675081824069 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873184743/5000000000 : ℝ)^65 ≤ (2469507736507/25000000000000 : ℝ)^49 := by
    have hnat : (873184743 : ℕ)^65*25000000000000^49 ≤ 2469507736507^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873184743 5000000000 2469507736507 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4280551/10000000 : ℝ), (6604225419/10000000000 : ℝ), (-873184743/5000000000 : ℝ)] ![(32446887220873/100000000000000 : ℝ), (57675081824069/100000000000000 : ℝ), (2469507736507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4280551/10000000 : ℝ)|^65 ≤ (32446887220873/100000000000000 : ℝ)^49
        have hw : |(4280551/10000000 : ℝ)|=(4280551/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6604225419/10000000000 : ℝ)|^65 ≤ (57675081824069/100000000000000 : ℝ)^49
        have hw : |(6604225419/10000000000 : ℝ)|=(6604225419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-873184743/5000000000 : ℝ)|^65 ≤ (2469507736507/25000000000000 : ℝ)^49
        have hw : |(-873184743/5000000000 : ℝ)|=(873184743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-33146229/1000000000 : ℝ)*x 0 + (6490646631/10000000000 : ℝ)*x 1 + (131270273/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33146229/1000000000 : ℝ)^65 ≤ (68106818483/6250000000000 : ℝ)^49 := by
    have hnat : (33146229 : ℕ)^65*6250000000000^49 ≤ 68106818483^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33146229 1000000000 68106818483 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6490646631/10000000000 : ℝ)^65 ≤ (56363018045783/100000000000000 : ℝ)^49 := by
    have hnat : (6490646631 : ℕ)^65*100000000000000^49 ≤ 56363018045783^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6490646631 10000000000 56363018045783 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131270273/250000000 : ℝ)^65 ≤ (2127363641983/5000000000000 : ℝ)^49 := by
    have hnat : (131270273 : ℕ)^65*5000000000000^49 ≤ 2127363641983^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131270273 250000000 2127363641983 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33146229/1000000000 : ℝ), (6490646631/10000000000 : ℝ), (131270273/250000000 : ℝ)] ![(68106818483/6250000000000 : ℝ), (56363018045783/100000000000000 : ℝ), (2127363641983/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33146229/1000000000 : ℝ)|^65 ≤ (68106818483/6250000000000 : ℝ)^49
        have hw : |(-33146229/1000000000 : ℝ)|=(33146229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6490646631/10000000000 : ℝ)|^65 ≤ (56363018045783/100000000000000 : ℝ)^49
        have hw : |(6490646631/10000000000 : ℝ)|=(6490646631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131270273/250000000 : ℝ)|^65 ≤ (2127363641983/5000000000000 : ℝ)^49
        have hw : |(131270273/250000000 : ℝ)|=(131270273/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5295850653/10000000000 : ℝ)*x 0 + (2687691937/10000000000 : ℝ)*x 1 + (1240408817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295850653/10000000000 : ℝ)^65 ≤ (1075801888867/2500000000000 : ℝ)^49 := by
    have hnat : (5295850653 : ℕ)^65*2500000000000^49 ≤ 1075801888867^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295850653 10000000000 1075801888867 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687691937/10000000000 : ℝ)^65 ≤ (3500131967431/20000000000000 : ℝ)^49 := by
    have hnat : (2687691937 : ℕ)^65*20000000000000^49 ≤ 3500131967431^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687691937 10000000000 3500131967431 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1240408817/2500000000 : ℝ)^65 ≤ (39467264593553/100000000000000 : ℝ)^49 := by
    have hnat : (1240408817 : ℕ)^65*100000000000000^49 ≤ 39467264593553^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240408817 2500000000 39467264593553 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5295850653/10000000000 : ℝ), (2687691937/10000000000 : ℝ), (1240408817/2500000000 : ℝ)] ![(1075801888867/2500000000000 : ℝ), (3500131967431/20000000000000 : ℝ), (39467264593553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5295850653/10000000000 : ℝ)|^65 ≤ (1075801888867/2500000000000 : ℝ)^49
        have hw : |(-5295850653/10000000000 : ℝ)|=(5295850653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687691937/10000000000 : ℝ)|^65 ≤ (3500131967431/20000000000000 : ℝ)^49
        have hw : |(2687691937/10000000000 : ℝ)|=(2687691937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1240408817/2500000000 : ℝ)|^65 ≤ (39467264593553/100000000000000 : ℝ)^49
        have hw : |(1240408817/2500000000 : ℝ)|=(1240408817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4011403121/10000000000 : ℝ)*x 0 + (-55178983/5000000000 : ℝ)*x 1 + (1528109361/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4011403121/10000000000 : ℝ)^65 ≤ (29768736962601/100000000000000 : ℝ)^49 := by
    have hnat : (4011403121 : ℕ)^65*100000000000000^49 ≤ 29768736962601^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011403121 10000000000 29768736962601 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55178983/5000000000 : ℝ)^65 ≤ (253348989959/100000000000000 : ℝ)^49 := by
    have hnat : (55178983 : ℕ)^65*100000000000000^49 ≤ 253348989959^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55178983 5000000000 253348989959 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1528109361/2000000000 : ℝ)^65 ≤ (34988957017681/50000000000000 : ℝ)^49 := by
    have hnat : (1528109361 : ℕ)^65*50000000000000^49 ≤ 34988957017681^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528109361 2000000000 34988957017681 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4011403121/10000000000 : ℝ), (-55178983/5000000000 : ℝ), (1528109361/2000000000 : ℝ)] ![(29768736962601/100000000000000 : ℝ), (253348989959/100000000000000 : ℝ), (34988957017681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4011403121/10000000000 : ℝ)|^65 ≤ (29768736962601/100000000000000 : ℝ)^49
        have hw : |(4011403121/10000000000 : ℝ)|=(4011403121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55178983/5000000000 : ℝ)|^65 ≤ (253348989959/100000000000000 : ℝ)^49
        have hw : |(-55178983/5000000000 : ℝ)|=(55178983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1528109361/2000000000 : ℝ)|^65 ≤ (34988957017681/50000000000000 : ℝ)^49
        have hw : |(1528109361/2000000000 : ℝ)|=(1528109361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1193354573/5000000000 : ℝ)*x 0 + (1976504547/2500000000 : ℝ)*x 1 + (-2000523657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1193354573/5000000000 : ℝ)^65 ≤ (9343551929/62500000000 : ℝ)^49 := by
    have hnat : (1193354573 : ℕ)^65*62500000000^49 ≤ 9343551929^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193354573 5000000000 9343551929 62500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1976504547/2500000000 : ℝ)^65 ≤ (14644276010051/20000000000000 : ℝ)^49 := by
    have hnat : (1976504547 : ℕ)^65*20000000000000^49 ≤ 14644276010051^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976504547 2500000000 14644276010051 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2000523657/10000000000 : ℝ)^65 ≤ (5914468423349/50000000000000 : ℝ)^49 := by
    have hnat : (2000523657 : ℕ)^65*50000000000000^49 ≤ 5914468423349^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000523657 10000000000 5914468423349 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1193354573/5000000000 : ℝ), (1976504547/2500000000 : ℝ), (-2000523657/10000000000 : ℝ)] ![(9343551929/62500000000 : ℝ), (14644276010051/20000000000000 : ℝ), (5914468423349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1193354573/5000000000 : ℝ)|^65 ≤ (9343551929/62500000000 : ℝ)^49
        have hw : |(1193354573/5000000000 : ℝ)|=(1193354573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1976504547/2500000000 : ℝ)|^65 ≤ (14644276010051/20000000000000 : ℝ)^49
        have hw : |(1976504547/2500000000 : ℝ)|=(1976504547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2000523657/10000000000 : ℝ)|^65 ≤ (5914468423349/50000000000000 : ℝ)^49
        have hw : |(-2000523657/10000000000 : ℝ)|=(2000523657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-136546329/10000000000 : ℝ)*x 0 + (1989751847/2500000000 : ℝ)*x 1 + (1800138037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136546329/10000000000 : ℝ)^65 ≤ (168020347757/50000000000000 : ℝ)^49 := by
    have hnat : (136546329 : ℕ)^65*50000000000000^49 ≤ 168020347757^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136546329 10000000000 168020347757 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989751847/2500000000 : ℝ)^65 ≤ (73873096979569/100000000000000 : ℝ)^49 := by
    have hnat : (1989751847 : ℕ)^65*100000000000000^49 ≤ 73873096979569^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989751847 2500000000 73873096979569 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1800138037/5000000000 : ℝ)^65 ≤ (25790862309589/100000000000000 : ℝ)^49 := by
    have hnat : (1800138037 : ℕ)^65*100000000000000^49 ≤ 25790862309589^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800138037 5000000000 25790862309589 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136546329/10000000000 : ℝ), (1989751847/2500000000 : ℝ), (1800138037/5000000000 : ℝ)] ![(168020347757/50000000000000 : ℝ), (73873096979569/100000000000000 : ℝ), (25790862309589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136546329/10000000000 : ℝ)|^65 ≤ (168020347757/50000000000000 : ℝ)^49
        have hw : |(-136546329/10000000000 : ℝ)|=(136546329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1989751847/2500000000 : ℝ)|^65 ≤ (73873096979569/100000000000000 : ℝ)^49
        have hw : |(1989751847/2500000000 : ℝ)|=(1989751847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1800138037/5000000000 : ℝ)|^65 ≤ (25790862309589/100000000000000 : ℝ)^49
        have hw : |(1800138037/5000000000 : ℝ)|=(1800138037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1517646539/2500000000 : ℝ)*x 0 + (2337859461/10000000000 : ℝ)*x 1 + (2211093993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1517646539/2500000000 : ℝ)^65 ≤ (25788067331537/50000000000000 : ℝ)^49 := by
    have hnat : (1517646539 : ℕ)^65*50000000000000^49 ≤ 25788067331537^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517646539 2500000000 25788067331537 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2337859461/10000000000 : ℝ)^65 ≤ (3636288184061/25000000000000 : ℝ)^49 := by
    have hnat : (2337859461 : ℕ)^65*25000000000000^49 ≤ 3636288184061^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337859461 10000000000 3636288184061 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211093993/5000000000 : ℝ)^65 ≤ (33878712583503/100000000000000 : ℝ)^49 := by
    have hnat : (2211093993 : ℕ)^65*100000000000000^49 ≤ 33878712583503^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211093993 5000000000 33878712583503 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1517646539/2500000000 : ℝ), (2337859461/10000000000 : ℝ), (2211093993/5000000000 : ℝ)] ![(25788067331537/50000000000000 : ℝ), (3636288184061/25000000000000 : ℝ), (33878712583503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1517646539/2500000000 : ℝ)|^65 ≤ (25788067331537/50000000000000 : ℝ)^49
        have hw : |(-1517646539/2500000000 : ℝ)|=(1517646539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2337859461/10000000000 : ℝ)|^65 ≤ (3636288184061/25000000000000 : ℝ)^49
        have hw : |(2337859461/10000000000 : ℝ)|=(2337859461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2211093993/5000000000 : ℝ)|^65 ≤ (33878712583503/100000000000000 : ℝ)^49
        have hw : |(2211093993/5000000000 : ℝ)|=(2211093993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6250339053/10000000000 : ℝ)*x 0 + (-120445579/10000000000 : ℝ)*x 1 + (5578389777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6250339053/10000000000 : ℝ)^65 ≤ (53611733046611/100000000000000 : ℝ)^49 := by
    have hnat : (6250339053 : ℕ)^65*100000000000000^49 ≤ 53611733046611^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6250339053 10000000000 53611733046611 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120445579/10000000000 : ℝ)^65 ≤ (142259190703/50000000000000 : ℝ)^49 := by
    have hnat : (120445579 : ℕ)^65*50000000000000^49 ≤ 142259190703^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120445579 10000000000 142259190703 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5578389777/10000000000 : ℝ)^65 ≤ (46103748552229/100000000000000 : ℝ)^49 := by
    have hnat : (5578389777 : ℕ)^65*100000000000000^49 ≤ 46103748552229^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5578389777 10000000000 46103748552229 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6250339053/10000000000 : ℝ), (-120445579/10000000000 : ℝ), (5578389777/10000000000 : ℝ)] ![(53611733046611/100000000000000 : ℝ), (142259190703/50000000000000 : ℝ), (46103748552229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6250339053/10000000000 : ℝ)|^65 ≤ (53611733046611/100000000000000 : ℝ)^49
        have hw : |(6250339053/10000000000 : ℝ)|=(6250339053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120445579/10000000000 : ℝ)|^65 ≤ (142259190703/50000000000000 : ℝ)^49
        have hw : |(-120445579/10000000000 : ℝ)|=(120445579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5578389777/10000000000 : ℝ)|^65 ≤ (46103748552229/100000000000000 : ℝ)^49
        have hw : |(5578389777/10000000000 : ℝ)|=(5578389777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1887645783/5000000000 : ℝ)*x 0 + (6447434083/10000000000 : ℝ)*x 1 + (-518123907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1887645783/5000000000 : ℝ)^65 ≤ (27467041576953/100000000000000 : ℝ)^49 := by
    have hnat : (1887645783 : ℕ)^65*100000000000000^49 ≤ 27467041576953^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887645783 5000000000 27467041576953 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6447434083/10000000000 : ℝ)^65 ≤ (55865784526017/100000000000000 : ℝ)^49 := by
    have hnat : (6447434083 : ℕ)^65*100000000000000^49 ≤ 55865784526017^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6447434083 10000000000 55865784526017 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518123907/2000000000 : ℝ)^65 ≤ (8333586940117/50000000000000 : ℝ)^49 := by
    have hnat : (518123907 : ℕ)^65*50000000000000^49 ≤ 8333586940117^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518123907 2000000000 8333586940117 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1887645783/5000000000 : ℝ), (6447434083/10000000000 : ℝ), (-518123907/2000000000 : ℝ)] ![(27467041576953/100000000000000 : ℝ), (55865784526017/100000000000000 : ℝ), (8333586940117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1887645783/5000000000 : ℝ)|^65 ≤ (27467041576953/100000000000000 : ℝ)^49
        have hw : |(1887645783/5000000000 : ℝ)|=(1887645783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6447434083/10000000000 : ℝ)|^65 ≤ (55865784526017/100000000000000 : ℝ)^49
        have hw : |(6447434083/10000000000 : ℝ)|=(6447434083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-518123907/2000000000 : ℝ)|^65 ≤ (8333586940117/50000000000000 : ℝ)^49
        have hw : |(-518123907/2000000000 : ℝ)|=(518123907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-395614941/10000000000 : ℝ)*x 0 + (2147958187/5000000000 : ℝ)*x 1 + (7312499029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (395614941/10000000000 : ℝ)^65 ≤ (1377968456307/100000000000000 : ℝ)^49 := by
    have hnat : (395614941 : ℕ)^65*100000000000000^49 ≤ 1377968456307^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395614941 10000000000 1377968456307 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147958187/5000000000 : ℝ)^65 ≤ (4075184947131/12500000000000 : ℝ)^49 := by
    have hnat : (2147958187 : ℕ)^65*12500000000000^49 ≤ 4075184947131^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147958187 5000000000 4075184947131 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7312499029/10000000000 : ℝ)^65 ≤ (33010275977643/50000000000000 : ℝ)^49 := by
    have hnat : (7312499029 : ℕ)^65*50000000000000^49 ≤ 33010275977643^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7312499029 10000000000 33010275977643 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-395614941/10000000000 : ℝ), (2147958187/5000000000 : ℝ), (7312499029/10000000000 : ℝ)] ![(1377968456307/100000000000000 : ℝ), (4075184947131/12500000000000 : ℝ), (33010275977643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-395614941/10000000000 : ℝ)|^65 ≤ (1377968456307/100000000000000 : ℝ)^49
        have hw : |(-395614941/10000000000 : ℝ)|=(395614941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2147958187/5000000000 : ℝ)|^65 ≤ (4075184947131/12500000000000 : ℝ)^49
        have hw : |(2147958187/5000000000 : ℝ)|=(2147958187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7312499029/10000000000 : ℝ)|^65 ≤ (33010275977643/50000000000000 : ℝ)^49
        have hw : |(7312499029/10000000000 : ℝ)|=(7312499029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-6422458691/10000000000 : ℝ)*x 0 + (3449035577/10000000000 : ℝ)*x 1 + (2978679641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6422458691/10000000000 : ℝ)^65 ≤ (55578895728749/100000000000000 : ℝ)^49 := by
    have hnat : (6422458691 : ℕ)^65*100000000000000^49 ≤ 55578895728749^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6422458691 10000000000 55578895728749 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3449035577/10000000000 : ℝ)^65 ≤ (6090904936679/25000000000000 : ℝ)^49 := by
    have hnat : (3449035577 : ℕ)^65*25000000000000^49 ≤ 6090904936679^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3449035577 10000000000 6090904936679 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2978679641/10000000000 : ℝ)^65 ≤ (5014371127661/25000000000000 : ℝ)^49 := by
    have hnat : (2978679641 : ℕ)^65*25000000000000^49 ≤ 5014371127661^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2978679641 10000000000 5014371127661 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6422458691/10000000000 : ℝ), (3449035577/10000000000 : ℝ), (2978679641/10000000000 : ℝ)] ![(55578895728749/100000000000000 : ℝ), (6090904936679/25000000000000 : ℝ), (5014371127661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6422458691/10000000000 : ℝ)|^65 ≤ (55578895728749/100000000000000 : ℝ)^49
        have hw : |(-6422458691/10000000000 : ℝ)|=(6422458691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3449035577/10000000000 : ℝ)|^65 ≤ (6090904936679/25000000000000 : ℝ)^49
        have hw : |(3449035577/10000000000 : ℝ)|=(3449035577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2978679641/10000000000 : ℝ)|^65 ≤ (5014371127661/25000000000000 : ℝ)^49
        have hw : |(2978679641/10000000000 : ℝ)|=(2978679641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2185772833/5000000000 : ℝ)*x 0 + (-317209377/2500000000 : ℝ)*x 1 + (1704592391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185772833/5000000000 : ℝ)^65 ≤ (33365017145427/100000000000000 : ℝ)^49 := by
    have hnat : (2185772833 : ℕ)^65*100000000000000^49 ≤ 33365017145427^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185772833 5000000000 33365017145427 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317209377/2500000000 : ℝ)^65 ≤ (6466073296397/100000000000000 : ℝ)^49 := by
    have hnat : (317209377 : ℕ)^65*100000000000000^49 ≤ 6466073296397^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317209377 2500000000 6466073296397 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704592391/2500000000 : ℝ)^65 ≤ (30084454768477/50000000000000 : ℝ)^49 := by
    have hnat : (1704592391 : ℕ)^65*50000000000000^49 ≤ 30084454768477^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704592391 2500000000 30084454768477 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185772833/5000000000 : ℝ), (-317209377/2500000000 : ℝ), (1704592391/2500000000 : ℝ)] ![(33365017145427/100000000000000 : ℝ), (6466073296397/100000000000000 : ℝ), (30084454768477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185772833/5000000000 : ℝ)|^65 ≤ (33365017145427/100000000000000 : ℝ)^49
        have hw : |(2185772833/5000000000 : ℝ)|=(2185772833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-317209377/2500000000 : ℝ)|^65 ≤ (6466073296397/100000000000000 : ℝ)^49
        have hw : |(-317209377/2500000000 : ℝ)|=(317209377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1704592391/2500000000 : ℝ)|^65 ≤ (30084454768477/50000000000000 : ℝ)^49
        have hw : |(1704592391/2500000000 : ℝ)|=(1704592391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3272722743/5000000000 : ℝ)*x 0 + (5024869739/10000000000 : ℝ)*x 1 + (-343822287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3272722743/5000000000 : ℝ)^65 ≤ (28497563635411/50000000000000 : ℝ)^49 := by
    have hnat : (3272722743 : ℕ)^65*50000000000000^49 ≤ 28497563635411^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3272722743 5000000000 28497563635411 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5024869739/10000000000 : ℝ)^65 ≤ (2006794549429/5000000000000 : ℝ)^49 := by
    have hnat : (5024869739 : ℕ)^65*5000000000000^49 ≤ 2006794549429^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024869739 10000000000 2006794549429 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343822287/5000000000 : ℝ)^65 ≤ (1434490863719/50000000000000 : ℝ)^49 := by
    have hnat : (343822287 : ℕ)^65*50000000000000^49 ≤ 1434490863719^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343822287 5000000000 1434490863719 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3272722743/5000000000 : ℝ), (5024869739/10000000000 : ℝ), (-343822287/5000000000 : ℝ)] ![(28497563635411/50000000000000 : ℝ), (2006794549429/5000000000000 : ℝ), (1434490863719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3272722743/5000000000 : ℝ)|^65 ≤ (28497563635411/50000000000000 : ℝ)^49
        have hw : |(3272722743/5000000000 : ℝ)|=(3272722743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5024869739/10000000000 : ℝ)|^65 ≤ (2006794549429/5000000000000 : ℝ)^49
        have hw : |(5024869739/10000000000 : ℝ)|=(5024869739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343822287/5000000000 : ℝ)|^65 ≤ (1434490863719/50000000000000 : ℝ)^49
        have hw : |(-343822287/5000000000 : ℝ)|=(343822287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s0_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-380668793/10000000000 : ℝ)*x 0 + (8147097/9765625 : ℝ)*x 1 + (2978679641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (380668793/10000000000 : ℝ)^65 ≤ (654670108661/50000000000000 : ℝ)^49 := by
    have hnat : (380668793 : ℕ)^65*50000000000000^49 ≤ 654670108661^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380668793 10000000000 654670108661 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8147097/9765625 : ℝ)^65 ≤ (78633175257463/100000000000000 : ℝ)^49 := by
    have hnat : (8147097 : ℕ)^65*100000000000000^49 ≤ 78633175257463^49*9765625^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8147097 9765625 78633175257463 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2978679641/10000000000 : ℝ)^65 ≤ (5014371127661/25000000000000 : ℝ)^49 := by
    have hnat : (2978679641 : ℕ)^65*25000000000000^49 ≤ 5014371127661^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2978679641 10000000000 5014371127661 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-380668793/10000000000 : ℝ), (8147097/9765625 : ℝ), (2978679641/10000000000 : ℝ)] ![(654670108661/50000000000000 : ℝ), (78633175257463/100000000000000 : ℝ), (5014371127661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-380668793/10000000000 : ℝ)|^65 ≤ (654670108661/50000000000000 : ℝ)^49
        have hw : |(-380668793/10000000000 : ℝ)|=(380668793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8147097/9765625 : ℝ)|^65 ≤ (78633175257463/100000000000000 : ℝ)^49
        have hw : |(8147097/9765625 : ℝ)|=(8147097/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2978679641/10000000000 : ℝ)|^65 ≤ (5014371127661/25000000000000 : ℝ)^49
        have hw : |(2978679641/10000000000 : ℝ)|=(2978679641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-66154517/125000000 : ℝ)*x 0 + (77537413/200000000 : ℝ)*x 1 + (3887361781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66154517/125000000 : ℝ)^65 ≤ (21497234456441/50000000000000 : ℝ)^49 := by
    have hnat : (66154517 : ℕ)^65*50000000000000^49 ≤ 21497234456441^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66154517 125000000 21497234456441 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77537413/200000000 : ℝ)^65 ≤ (28451676484053/100000000000000 : ℝ)^49 := by
    have hnat : (77537413 : ℕ)^65*100000000000000^49 ≤ 28451676484053^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77537413 200000000 28451676484053 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3887361781/10000000000 : ℝ)^65 ≤ (28553854591367/100000000000000 : ℝ)^49 := by
    have hnat : (3887361781 : ℕ)^65*100000000000000^49 ≤ 28553854591367^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3887361781 10000000000 28553854591367 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66154517/125000000 : ℝ), (77537413/200000000 : ℝ), (3887361781/10000000000 : ℝ)] ![(21497234456441/50000000000000 : ℝ), (28451676484053/100000000000000 : ℝ), (28553854591367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66154517/125000000 : ℝ)|^65 ≤ (21497234456441/50000000000000 : ℝ)^49
        have hw : |(-66154517/125000000 : ℝ)|=(66154517/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77537413/200000000 : ℝ)|^65 ≤ (28451676484053/100000000000000 : ℝ)^49
        have hw : |(77537413/200000000 : ℝ)|=(77537413/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3887361781/10000000000 : ℝ)|^65 ≤ (28553854591367/100000000000000 : ℝ)^49
        have hw : |(3887361781/10000000000 : ℝ)|=(3887361781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (576621203/1250000000 : ℝ)*x 0 + (-3109407273/10000000000 : ℝ)*x 1 + (1057376339/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (576621203/1250000000 : ℝ)^65 ≤ (4478885764287/12500000000000 : ℝ)^49 := by
    have hnat : (576621203 : ℕ)^65*12500000000000^49 ≤ 4478885764287^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576621203 1250000000 4478885764287 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3109407273/10000000000 : ℝ)^65 ≤ (21233486943659/100000000000000 : ℝ)^49 := by
    have hnat : (3109407273 : ℕ)^65*100000000000000^49 ≤ 21233486943659^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3109407273 10000000000 21233486943659 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057376339/2000000000 : ℝ)^65 ≤ (42935426928427/100000000000000 : ℝ)^49 := by
    have hnat : (1057376339 : ℕ)^65*100000000000000^49 ≤ 42935426928427^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057376339 2000000000 42935426928427 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(576621203/1250000000 : ℝ), (-3109407273/10000000000 : ℝ), (1057376339/2000000000 : ℝ)] ![(4478885764287/12500000000000 : ℝ), (21233486943659/100000000000000 : ℝ), (42935426928427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(576621203/1250000000 : ℝ)|^65 ≤ (4478885764287/12500000000000 : ℝ)^49
        have hw : |(576621203/1250000000 : ℝ)|=(576621203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3109407273/10000000000 : ℝ)|^65 ≤ (21233486943659/100000000000000 : ℝ)^49
        have hw : |(-3109407273/10000000000 : ℝ)|=(3109407273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057376339/2000000000 : ℝ)|^65 ≤ (42935426928427/100000000000000 : ℝ)^49
        have hw : |(1057376339/2000000000 : ℝ)|=(1057376339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (933189587/2000000000 : ℝ)*x 0 + (1293823161/2500000000 : ℝ)*x 1 + (-1590506827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933189587/2000000000 : ℝ)^65 ≤ (36377983989569/100000000000000 : ℝ)^49 := by
    have hnat : (933189587 : ℕ)^65*100000000000000^49 ≤ 36377983989569^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933189587 2000000000 36377983989569 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293823161/2500000000 : ℝ)^65 ≤ (10434362323997/25000000000000 : ℝ)^49 := by
    have hnat : (1293823161 : ℕ)^65*25000000000000^49 ≤ 10434362323997^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293823161 2500000000 10434362323997 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1590506827/5000000000 : ℝ)^65 ≤ (21884566699163/100000000000000 : ℝ)^49 := by
    have hnat : (1590506827 : ℕ)^65*100000000000000^49 ≤ 21884566699163^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590506827 5000000000 21884566699163 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(933189587/2000000000 : ℝ), (1293823161/2500000000 : ℝ), (-1590506827/5000000000 : ℝ)] ![(36377983989569/100000000000000 : ℝ), (10434362323997/25000000000000 : ℝ), (21884566699163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(933189587/2000000000 : ℝ)|^65 ≤ (36377983989569/100000000000000 : ℝ)^49
        have hw : |(933189587/2000000000 : ℝ)|=(933189587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293823161/2500000000 : ℝ)|^65 ≤ (10434362323997/25000000000000 : ℝ)^49
        have hw : |(1293823161/2500000000 : ℝ)|=(1293823161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1590506827/5000000000 : ℝ)|^65 ≤ (21884566699163/100000000000000 : ℝ)^49
        have hw : |(-1590506827/5000000000 : ℝ)|=(1590506827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301027_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (579505559/5000000000 : ℝ)*x 0 + (5859897693/10000000000 : ℝ)*x 1 + (548204599/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (579505559/5000000000 : ℝ)^65 ≤ (5734341507593/100000000000000 : ℝ)^49 := by
    have hnat : (579505559 : ℕ)^65*100000000000000^49 ≤ 5734341507593^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579505559 5000000000 5734341507593 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5859897693/10000000000 : ℝ)^65 ≤ (49215173948809/100000000000000 : ℝ)^49 := by
    have hnat : (5859897693 : ℕ)^65*100000000000000^49 ≤ 49215173948809^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5859897693 10000000000 49215173948809 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548204599/1000000000 : ℝ)^65 ≤ (22525242265907/50000000000000 : ℝ)^49 := by
    have hnat : (548204599 : ℕ)^65*50000000000000^49 ≤ 22525242265907^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548204599 1000000000 22525242265907 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(579505559/5000000000 : ℝ), (5859897693/10000000000 : ℝ), (548204599/1000000000 : ℝ)] ![(5734341507593/100000000000000 : ℝ), (49215173948809/100000000000000 : ℝ), (22525242265907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(579505559/5000000000 : ℝ)|^65 ≤ (5734341507593/100000000000000 : ℝ)^49
        have hw : |(579505559/5000000000 : ℝ)|=(579505559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5859897693/10000000000 : ℝ)|^65 ≤ (49215173948809/100000000000000 : ℝ)^49
        have hw : |(5859897693/10000000000 : ℝ)|=(5859897693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548204599/1000000000 : ℝ)|^65 ≤ (22525242265907/50000000000000 : ℝ)^49
        have hw : |(548204599/1000000000 : ℝ)|=(548204599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301027 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((4552100083/10000000000 : ℝ)*X 1 0+(-57330821/400000000 : ℝ)*X 1 1+(820334297/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4280551/10000000 : ℝ)*X 2 0+(6604225419/10000000000 : ℝ)*X 2 1+(-873184743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((-33146229/1000000000 : ℝ)*X 0 0+(6490646631/10000000000 : ℝ)*X 0 1+(131270273/250000000 : ℝ)*X 0 2+(-33146229/1000000000 : ℝ)*X 1 0+(6490646631/10000000000 : ℝ)*X 1 1+(131270273/250000000 : ℝ)*X 1 2+(-33146229/1000000000 : ℝ)*X 2 0+(6490646631/10000000000 : ℝ)*X 2 1+(131270273/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-5295850653/10000000000 : ℝ)*X 0 0+(2687691937/10000000000 : ℝ)*X 0 1+(1240408817/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4011403121/10000000000 : ℝ)*X 1 0+(-55178983/5000000000 : ℝ)*X 1 1+(1528109361/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1193354573/5000000000 : ℝ)*X 2 0+(1976504547/2500000000 : ℝ)*X 2 1+(-2000523657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-136546329/10000000000 : ℝ)*X 0 0+(1989751847/2500000000 : ℝ)*X 0 1+(1800138037/5000000000 : ℝ)*X 0 2+(-136546329/10000000000 : ℝ)*X 1 0+(1989751847/2500000000 : ℝ)*X 1 1+(1800138037/5000000000 : ℝ)*X 1 2+(-136546329/10000000000 : ℝ)*X 2 0+(1989751847/2500000000 : ℝ)*X 2 1+(1800138037/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1517646539/2500000000 : ℝ)*X 0 0+(2337859461/10000000000 : ℝ)*X 0 1+(2211093993/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((6250339053/10000000000 : ℝ)*X 1 0+(-120445579/10000000000 : ℝ)*X 1 1+(5578389777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1887645783/5000000000 : ℝ)*X 2 0+(6447434083/10000000000 : ℝ)*X 2 1+(-518123907/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-395614941/10000000000 : ℝ)*X 0 0+(2147958187/5000000000 : ℝ)*X 0 1+(7312499029/10000000000 : ℝ)*X 0 2+(-395614941/10000000000 : ℝ)*X 1 0+(2147958187/5000000000 : ℝ)*X 1 1+(7312499029/10000000000 : ℝ)*X 1 2+(-395614941/10000000000 : ℝ)*X 2 0+(2147958187/5000000000 : ℝ)*X 2 1+(7312499029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-6422458691/10000000000 : ℝ)*X 0 0+(3449035577/10000000000 : ℝ)*X 0 1+(2978679641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2185772833/5000000000 : ℝ)*X 1 0+(-317209377/2500000000 : ℝ)*X 1 1+(1704592391/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3272722743/5000000000 : ℝ)*X 2 0+(5024869739/10000000000 : ℝ)*X 2 1+(-343822287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-380668793/10000000000 : ℝ)*X 0 0+(8147097/9765625 : ℝ)*X 0 1+(2978679641/10000000000 : ℝ)*X 0 2+(-380668793/10000000000 : ℝ)*X 1 0+(8147097/9765625 : ℝ)*X 1 1+(2978679641/10000000000 : ℝ)*X 1 2+(-380668793/10000000000 : ℝ)*X 2 0+(8147097/9765625 : ℝ)*X 2 1+(2978679641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((17593/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17593/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2918682754552282749447/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (657452198697/1000000000000 : ℝ)*(base7) + (186748703187/1000000000000 : ℝ)*(base39) + (41639272119/100000000000 : ℝ)*(base50) + (3094157/250000000000 : ℝ)*(base53) + (50603161123/1000000000000 : ℝ)*(base60) + (2006396548349/1000000000000 : ℝ)*(major_s0_0) + (2006396548349/1000000000000 : ℝ)*(major_s0_1) + (1003192085861/500000000000 : ℝ)*(major_s0_2) + (2881433/500000000000 : ℝ)*(sp_s0_6) + (2251457809279/1000000000000 : ℝ)*(sp_s0_7) + (1125703328293/500000000000 : ℝ)*(sp_s0_8) + (2251470185907/1000000000000 : ℝ)*(sp_s0_9) + (2013816293561/1000000000000 : ℝ)*(sp_s0_13) + (25576347/500000000000 : ℝ)*(sp_s0_22) + (1356369857731/1000000000000 : ℝ)*(f.failure) + (2251470185907/1000000000000 : ℝ)*(f.sum) + (4887626267100781/10000000000000000000000000000 : ℝ)*base62 + (2047316533181377/5000000000000000000000000000 : ℝ)*base64 + (6324199547578407/10000000000000000000000000000 : ℝ)*base67 + (5923453706824471/5000000000000000000000000000 : ℝ)*base68 + (114156372982183/2000000000000000000000000000 : ℝ)*base70 + (3247538173578407/10000000000000000000000000000 : ℝ)*base73 + (3852851863451839/10000000000000000000000000000 : ℝ)*base74 + (1849052479548161/10000000000000000000000000000 : ℝ)*base76 + (1974930386078407/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (25111/25000000000000000 : ℝ)*base87 + (25111/25000000000000000 : ℝ)*base89 + (111/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(78337/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(78337/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32230007493781248713211/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28676708343/25000000000 : ℝ)*(base1) + (59615916561/62500000000 : ℝ)*(base7) + (27579939531/125000000000 : ℝ)*(base40) + (45319/50000000000 : ℝ)*(base50) + (1186581/100000000000 : ℝ)*(base54) + (77290579123/200000000000 : ℝ)*(base60) + (2316105568659/1000000000000 : ℝ)*(major_s0_0) + (2316105568659/1000000000000 : ℝ)*(major_s0_1) + (2316093702849/1000000000000 : ℝ)*(major_s0_2) + (59222851/500000000000 : ℝ)*(sp_s0_2) + (72520354151/20000000000 : ℝ)*(sp_s0_14) + (247894937383/100000000000 : ℝ)*(sp_s0_15) + (2478819062317/1000000000000 : ℝ)*(sp_s0_16) + (5490058757/4000000000 : ℝ)*(sp_s0_20) + (391435055951/250000000000 : ℝ)*(f.failure) + (247894937383/100000000000 : ℝ)*(f.sum) + (1671265537843353/2500000000000000000000000000 : ℝ)*base63 + (4234860931078093/10000000000000000000000000000 : ℝ)*base64 + (881557888262263/10000000000000000000000000000 : ℝ)*base66 + (2992005169151339/10000000000000000000000000000 : ℝ)*base68 + (365090164599289/2500000000000000000000000000 : ℝ)*base71 + (3833399498262263/10000000000000000000000000000 : ℝ)*base72 + (1976970358524751/10000000000000000000000000000 : ℝ)*base75 + (511564520475249/10000000000000000000000000000 : ℝ)*base77 + (1317588579762263/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (5181/6250000000000000 : ℝ)*base87 + (5181/6250000000000000 : ℝ)*base89 + (5181/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(83837/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(83837/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (39500722009577462741229/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (363245196827/500000000000 : ℝ)*(base1) + (413289261039/500000000000 : ℝ)*(base7) + (4478071797/500000000000 : ℝ)*(base39) + (473053368649/1000000000000 : ℝ)*(base44) + (2684194117/7812500000 : ℝ)*(base50) + (2820323/1000000000000 : ℝ)*(base60) + (90204173537/40000000000 : ℝ)*(major_s0_0) + (111378185611/62500000000 : ℝ)*(major_s0_1) + (90204173537/40000000000 : ℝ)*(major_s0_2) + (275318453/1000000000000 : ℝ)*(sp_s0_1) + (640613805777/200000000000 : ℝ)*(sp_s0_21) + (62601560879/31250000000 : ℝ)*(sp_s0_22) + (247657863523/100000000000 : ℝ)*(sp_s0_23) + (575768379869/500000000000 : ℝ)*(sp_s0_27) + (1524501999963/1000000000000 : ℝ)*(f.failure) + (247657863523/100000000000 : ℝ)*(f.sum) + (3428288350029789/10000000000000000000000000000 : ℝ)*base63 + (377563785905709/400000000000000000000000000 : ℝ)*base64 + (235037751479627/625000000000000000000000000 : ℝ)*base66 + (216216139888907/400000000000000000000000000 : ℝ)*base68 + (142685105388401/200000000000000000000000000 : ℝ)*base70 + (135626540665709/400000000000000000000000000 : ℝ)*base72 + (84427619953279/625000000000000000000000000 : ℝ)*base75 + (175612405991093/400000000000000000000000000 : ℝ)*base76 + (2440035342683243/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (6703/25000000000000000 : ℝ)*base87 + (6703/25000000000000000 : ℝ)*base89 + (6703/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (17593/25000 : ℝ) ^ (129/32 : ℝ) ≤ (4851330010967660621/20000000000000000000 : ℝ) := by
    have hpowers : (17593/25000 : ℝ)^129 ≤ (4851330010967660621/20000000000000000000 : ℝ)^32 := by
      have hnat : (17593 : ℕ)^129*20000000000000000000^32 ≤ 4851330010967660621^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17593 25000 4851330010967660621 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17593/25000 : ℝ)) (X := (4851330010967660621/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (24851330010967660621/20000000000000000000 : ℝ) ≤ (2638378679964369/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (24851330010967660621/20000000000000000000 : ℝ)^32 ≤ (2638378679964369/2500000000000000 : ℝ)^129 := by
      have hnat : (24851330010967660621 : ℕ)^32*2500000000000000^129 ≤ 2638378679964369^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24851330010967660621 20000000000000000000 2638378679964369 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2638378679964369/2500000000000000 : ℝ)) (X := (24851330010967660621/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (14851330010967660621/10000000000000000000 : ℝ) ≤ (11030836781707787/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (14851330010967660621/10000000000000000000 : ℝ)^32 ≤ (11030836781707787/10000000000000000 : ℝ)^129 := by
      have hnat : (14851330010967660621 : ℕ)^32*10000000000000000^129 ≤ 11030836781707787^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14851330010967660621 10000000000000000000 11030836781707787 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11030836781707787/10000000000000000 : ℝ)) (X := (14851330010967660621/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(138378679964369/1759300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(477322061850311/7037200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (17593/25000 : ℝ)) (alpha := (138378679964369/1759300000000000 : ℝ)) (beta := (477322061850311/7037200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17593/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(138378679964369/1759300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(477322061850311/7037200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (78337/100000 : ℝ) ^ (129/32 : ℝ) ≤ (37372677201184427421/100000000000000000000 : ℝ) := by
    have hpowers : (78337/100000 : ℝ)^129 ≤ (37372677201184427421/100000000000000000000 : ℝ)^32 := by
      have hnat : (78337 : ℕ)^129*100000000000000000000^32 ≤ 37372677201184427421^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78337 100000 37372677201184427421 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (78337/100000 : ℝ)) (X := (37372677201184427421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (137372677201184427421/100000000000000000000 : ℝ) ≤ (10819516206319153/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (137372677201184427421/100000000000000000000 : ℝ)^32 ≤ (10819516206319153/10000000000000000 : ℝ)^129 := by
      have hnat : (137372677201184427421 : ℕ)^32*10000000000000000^129 ≤ 10819516206319153^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        137372677201184427421 100000000000000000000 10819516206319153 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10819516206319153/10000000000000000 : ℝ)) (X := (137372677201184427421/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (87372677201184427421/50000000000000000000 : ℝ) ≤ (57425083542647/50000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (87372677201184427421/50000000000000000000 : ℝ)^32 ≤ (57425083542647/50000000000000 : ℝ)^129 := by
      have hnat : (87372677201184427421 : ℕ)^32*50000000000000^129 ≤ 57425083542647^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87372677201184427421 50000000000000000000 57425083542647 50000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (57425083542647/50000000000000 : ℝ)) (X := (87372677201184427421/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(117073743759879/1119100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(665500502210247/7833700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (78337/100000 : ℝ)) (alpha := (117073743759879/1119100000000000 : ℝ)) (beta := (665500502210247/7833700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (78337/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(117073743759879/1119100000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(665500502210247/7833700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (83837/100000 : ℝ) ^ (129/32 : ℝ) ≤ (12282599533775575229/25000000000000000000 : ℝ) := by
    have hpowers : (83837/100000 : ℝ)^129 ≤ (12282599533775575229/25000000000000000000 : ℝ)^32 := by
      have hnat : (83837 : ℕ)^129*25000000000000000000^32 ≤ 12282599533775575229^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83837 100000 12282599533775575229 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83837/100000 : ℝ)) (X := (12282599533775575229/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (37282599533775575229/25000000000000000000 : ℝ) ≤ (11042188985712443/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (37282599533775575229/25000000000000000000 : ℝ)^32 ≤ (11042188985712443/10000000000000000 : ℝ)^129 := by
      have hnat : (37282599533775575229 : ℕ)^32*10000000000000000^129 ≤ 11042188985712443^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37282599533775575229 25000000000000000000 11042188985712443 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11042188985712443/10000000000000000 : ℝ)) (X := (37282599533775575229/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (24782599533775575229/12500000000000000000 : ℝ) ≤ (11850404401204431/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (24782599533775575229/12500000000000000000 : ℝ)^32 ≤ (11850404401204431/10000000000000000 : ℝ)^129 := by
      have hnat : (24782599533775575229 : ℕ)^32*10000000000000000^129 ≤ 11850404401204431^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24782599533775575229 12500000000000000000 11850404401204431 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11850404401204431/10000000000000000 : ℝ)) (X := (24782599533775575229/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1042188985712443/8383700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(202053853872997/2095925000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (83837/100000 : ℝ)) (alpha := (1042188985712443/8383700000000000 : ℝ)) (beta := (202053853872997/2095925000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (83837/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1042188985712443/8383700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(202053853872997/2095925000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-66154517/125000000 : ℝ)*X 0 0+(77537413/200000000 : ℝ)*X 0 1+(3887361781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((576621203/1250000000 : ℝ)*X 1 0+(-3109407273/10000000000 : ℝ)*X 1 1+(1057376339/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((933189587/2000000000 : ℝ)*X 2 0+(1293823161/2500000000 : ℝ)*X 2 1+(-1590506827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((579505559/5000000000 : ℝ)*X 0 0+(5859897693/10000000000 : ℝ)*X 0 1+(548204599/1000000000 : ℝ)*X 0 2+(579505559/5000000000 : ℝ)*X 1 0+(5859897693/10000000000 : ℝ)*X 1 1+(548204599/1000000000 : ℝ)*X 1 2+(579505559/5000000000 : ℝ)*X 2 0+(5859897693/10000000000 : ℝ)*X 2 1+(548204599/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301027_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-7430829227820177696225981300397179/1269700163087000000000000000000000 : ℝ) := by norm_num
    linear_combination (222607/500000000000 : ℝ)*(base1) + (23117/1000000000000 : ℝ)*(base5) + (253159/1000000000000 : ℝ)*(base8) + (346897/1000000000000 : ℝ)*(base19) + (25543/200000000000 : ℝ)*(base31) + (298351914991/1000000000000 : ℝ)*(base50) + (10969/100000000000 : ℝ)*(base53) + (34943800121/125000000000 : ℝ)*(base60) + (36981/25000 : ℝ)*(major_s1_0) + (36981/25000 : ℝ)*(major_s1_1) + (147923989031/100000000000 : ℝ)*(major_s1_2) + (1950809531673/1000000000000 : ℝ)*(sp_s1_0) + (1950808992721/1000000000000 : ℝ)*(sp_s1_1) + (78032378897/40000000000 : ℝ)*(sp_s1_2) + (499999701977/500000000000 : ℝ)*(sp_s1_6) + (487702362327/250000000000 : ℝ)*(f.sum) + (270728477324859141/721707590000000000000000000000 : ℝ)*base63 + (329784685059/8061250000000000000000000 : ℝ)*base64 + (4636127689057/111910000000000000000000000 : ℝ)*base67 + (1383242621567/12898000000000000000000000 : ℝ)*base69 + (33114359958121767/226914514000000000000000000000 : ℝ)*base71 + (11471628107577/35186000000000000000000000 : ℝ)*base73 + (32005797170123/111910000000000000000000000 : ℝ)*base75 + (394554135777/87965000000000000000000000 : ℝ)*base77 + (53635370644869687/196883263000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p001_b015 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 27 ≤ c.val) (hhi : c.val < 28)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=27 := by omega
  rcases hc with rfl
  · exact collision_c301027 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 27 ≤ c.val) (hhi : c.val < 28)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b015 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
