-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p021_b041
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:40:48.704662+00:00
-- url     : https://prove2.me/submissions/7e92effa-6021-49ca-9b7b-0d2d7e12855e

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
theorem collision_support_c321075_s0_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-9604303/1000000000 : ℝ)*x 0 + (-859696503/1250000000 : ℝ)*x 1 + (896066927/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9604303/1000000000 : ℝ)^41 ≤ (38929307539/12500000000000 : ℝ)^33 := by
    have hnat : (9604303 : ℕ)^41*12500000000000^33 ≤ 38929307539^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9604303 1000000000 38929307539 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859696503/1250000000 : ℝ)^41 ≤ (31404760822817/50000000000000 : ℝ)^33 := by
    have hnat : (859696503 : ℕ)^41*50000000000000^33 ≤ 31404760822817^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859696503 1250000000 31404760822817 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896066927/2000000000 : ℝ)^41 ≤ (7375808777461/20000000000000 : ℝ)^33 := by
    have hnat : (896066927 : ℕ)^41*20000000000000^33 ≤ 7375808777461^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896066927 2000000000 7375808777461 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9604303/1000000000 : ℝ), (-859696503/1250000000 : ℝ), (896066927/2000000000 : ℝ)] ![(38929307539/12500000000000 : ℝ), (31404760822817/50000000000000 : ℝ), (7375808777461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9604303/1000000000 : ℝ)|^41 ≤ (38929307539/12500000000000 : ℝ)^33
        have hw : |(-9604303/1000000000 : ℝ)|=(9604303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-859696503/1250000000 : ℝ)|^41 ≤ (31404760822817/50000000000000 : ℝ)^33
        have hw : |(-859696503/1250000000 : ℝ)|=(859696503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896066927/2000000000 : ℝ)|^41 ≤ (7375808777461/20000000000000 : ℝ)^33
        have hw : |(896066927/2000000000 : ℝ)|=(896066927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5535292427/10000000000 : ℝ)*x 0 + (-1753698317/5000000000 : ℝ)*x 1 + (-325901381/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5535292427/10000000000 : ℝ)^41 ≤ (38367332299/80000000000 : ℝ)^33 := by
    have hnat : (5535292427 : ℕ)^41*80000000000^33 ≤ 38367332299^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5535292427 10000000000 38367332299 80000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1753698317/5000000000 : ℝ)^41 ≤ (27206845181651/100000000000000 : ℝ)^33 := by
    have hnat : (1753698317 : ℕ)^41*100000000000000^33 ≤ 27206845181651^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1753698317 5000000000 27206845181651 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325901381/1000000000 : ℝ)^41 ≤ (4966797885359/20000000000000 : ℝ)^33 := by
    have hnat : (325901381 : ℕ)^41*20000000000000^33 ≤ 4966797885359^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325901381 1000000000 4966797885359 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5535292427/10000000000 : ℝ), (-1753698317/5000000000 : ℝ), (-325901381/1000000000 : ℝ)] ![(38367332299/80000000000 : ℝ), (27206845181651/100000000000000 : ℝ), (4966797885359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5535292427/10000000000 : ℝ)|^41 ≤ (38367332299/80000000000 : ℝ)^33
        have hw : |(5535292427/10000000000 : ℝ)|=(5535292427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1753698317/5000000000 : ℝ)|^41 ≤ (27206845181651/100000000000000 : ℝ)^33
        have hw : |(-1753698317/5000000000 : ℝ)|=(1753698317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-325901381/1000000000 : ℝ)|^41 ≤ (4966797885359/20000000000000 : ℝ)^33
        have hw : |(-325901381/1000000000 : ℝ)|=(325901381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_7 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-79352769/2000000000 : ℝ)*x 0 + (-207456471/250000000 : ℝ)*x 1 + (2612874991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79352769/2000000000 : ℝ)^41 ≤ (453651449327/25000000000000 : ℝ)^33 := by
    have hnat : (79352769 : ℕ)^41*25000000000000^33 ≤ 453651449327^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79352769 2000000000 453651449327 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207456471/250000000 : ℝ)^41 ≤ (79313562357151/100000000000000 : ℝ)^33 := by
    have hnat : (207456471 : ℕ)^41*100000000000000^33 ≤ 79313562357151^33*250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207456471 250000000 79313562357151 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612874991/10000000000 : ℝ)^41 ≤ (4717957959691/25000000000000 : ℝ)^33 := by
    have hnat : (2612874991 : ℕ)^41*25000000000000^33 ≤ 4717957959691^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612874991 10000000000 4717957959691 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79352769/2000000000 : ℝ), (-207456471/250000000 : ℝ), (2612874991/10000000000 : ℝ)] ![(453651449327/25000000000000 : ℝ), (79313562357151/100000000000000 : ℝ), (4717957959691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79352769/2000000000 : ℝ)|^41 ≤ (453651449327/25000000000000 : ℝ)^33
        have hw : |(-79352769/2000000000 : ℝ)|=(79352769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207456471/250000000 : ℝ)|^41 ≤ (79313562357151/100000000000000 : ℝ)^33
        have hw : |(-207456471/250000000 : ℝ)|=(207456471/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2612874991/10000000000 : ℝ)|^41 ≤ (4717957959691/25000000000000 : ℝ)^33
        have hw : |(2612874991/10000000000 : ℝ)|=(2612874991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_8 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (584532439/1000000000 : ℝ)*x 0 + (4148789417/10000000000 : ℝ)*x 1 + (2190795323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (584532439/1000000000 : ℝ)^41 ≤ (3207431504989/6250000000000 : ℝ)^33 := by
    have hnat : (584532439 : ℕ)^41*6250000000000^33 ≤ 3207431504989^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584532439 1000000000 3207431504989 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4148789417/10000000000 : ℝ)^41 ≤ (16759701477689/50000000000000 : ℝ)^33 := by
    have hnat : (4148789417 : ℕ)^41*50000000000000^33 ≤ 16759701477689^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148789417 10000000000 16759701477689 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190795323/10000000000 : ℝ)^41 ≤ (1516169295219/10000000000000 : ℝ)^33 := by
    have hnat : (2190795323 : ℕ)^41*10000000000000^33 ≤ 1516169295219^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190795323 10000000000 1516169295219 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(584532439/1000000000 : ℝ), (4148789417/10000000000 : ℝ), (2190795323/10000000000 : ℝ)] ![(3207431504989/6250000000000 : ℝ), (16759701477689/50000000000000 : ℝ), (1516169295219/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(584532439/1000000000 : ℝ)|^41 ≤ (3207431504989/6250000000000 : ℝ)^33
        have hw : |(584532439/1000000000 : ℝ)|=(584532439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4148789417/10000000000 : ℝ)|^41 ≤ (16759701477689/50000000000000 : ℝ)^33
        have hw : |(4148789417/10000000000 : ℝ)|=(4148789417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2190795323/10000000000 : ℝ)|^41 ≤ (1516169295219/10000000000000 : ℝ)^33
        have hw : |(2190795323/10000000000 : ℝ)|=(2190795323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_9 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1163723911/2000000000 : ℝ)*x 0 + (-143474637/400000000 : ℝ)*x 1 + (-2847252717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1163723911/2000000000 : ℝ)^41 ≤ (51027773564777/100000000000000 : ℝ)^33 := by
    have hnat : (1163723911 : ℕ)^41*100000000000000^33 ≤ 51027773564777^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163723911 2000000000 51027773564777 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143474637/400000000 : ℝ)^41 ≤ (27974819900013/100000000000000 : ℝ)^33 := by
    have hnat : (143474637 : ℕ)^41*100000000000000^33 ≤ 27974819900013^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143474637 400000000 27974819900013 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2847252717/10000000000 : ℝ)^41 ≤ (2099740651217/10000000000000 : ℝ)^33 := by
    have hnat : (2847252717 : ℕ)^41*10000000000000^33 ≤ 2099740651217^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847252717 10000000000 2099740651217 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1163723911/2000000000 : ℝ), (-143474637/400000000 : ℝ), (-2847252717/10000000000 : ℝ)] ![(51027773564777/100000000000000 : ℝ), (27974819900013/100000000000000 : ℝ), (2099740651217/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1163723911/2000000000 : ℝ)|^41 ≤ (51027773564777/100000000000000 : ℝ)^33
        have hw : |(1163723911/2000000000 : ℝ)|=(1163723911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-143474637/400000000 : ℝ)|^41 ≤ (27974819900013/100000000000000 : ℝ)^33
        have hw : |(-143474637/400000000 : ℝ)|=(143474637/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2847252717/10000000000 : ℝ)|^41 ≤ (2099740651217/10000000000000 : ℝ)^33
        have hw : |(-2847252717/10000000000 : ℝ)|=(2847252717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_13 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (223741449/2000000000 : ℝ)*x 0 + (-177073/500000000 : ℝ)*x 1 + (189332597/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223741449/2000000000 : ℝ)^41 ≤ (6578127045597/100000000000000 : ℝ)^33 := by
    have hnat : (223741449 : ℕ)^41*100000000000000^33 ≤ 6578127045597^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223741449 2000000000 6578127045597 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177073/500000000 : ℝ)^41 ≤ (5159652869/100000000000000 : ℝ)^33 := by
    have hnat : (177073 : ℕ)^41*100000000000000^33 ≤ 5159652869^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177073 500000000 5159652869 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189332597/200000000 : ℝ)^41 ≤ (93416713290541/100000000000000 : ℝ)^33 := by
    have hnat : (189332597 : ℕ)^41*100000000000000^33 ≤ 93416713290541^33*200000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189332597 200000000 93416713290541 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(223741449/2000000000 : ℝ), (-177073/500000000 : ℝ), (189332597/200000000 : ℝ)] ![(6578127045597/100000000000000 : ℝ), (5159652869/100000000000000 : ℝ), (93416713290541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(223741449/2000000000 : ℝ)|^41 ≤ (6578127045597/100000000000000 : ℝ)^33
        have hw : |(223741449/2000000000 : ℝ)|=(223741449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177073/500000000 : ℝ)|^41 ≤ (5159652869/100000000000000 : ℝ)^33
        have hw : |(-177073/500000000 : ℝ)|=(177073/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(189332597/200000000 : ℝ)|^41 ≤ (93416713290541/100000000000000 : ℝ)^33
        have hw : |(189332597/200000000 : ℝ)|=(189332597/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_14 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-102307581/10000000000 : ℝ)*x 0 + (-4544901281/10000000000 : ℝ)*x 1 + (852121129/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102307581/10000000000 : ℝ)^41 ≤ (84217284671/25000000000000 : ℝ)^33 := by
    have hnat : (102307581 : ℕ)^41*25000000000000^33 ≤ 84217284671^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102307581 10000000000 84217284671 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4544901281/10000000000 : ℝ)^41 ≤ (300324018721/800000000000 : ℝ)^33 := by
    have hnat : (4544901281 : ℕ)^41*800000000000^33 ≤ 300324018721^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544901281 10000000000 300324018721 800000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (852121129/1250000000 : ℝ)^41 ≤ (62122628513923/100000000000000 : ℝ)^33 := by
    have hnat : (852121129 : ℕ)^41*100000000000000^33 ≤ 62122628513923^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852121129 1250000000 62122628513923 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102307581/10000000000 : ℝ), (-4544901281/10000000000 : ℝ), (852121129/1250000000 : ℝ)] ![(84217284671/25000000000000 : ℝ), (300324018721/800000000000 : ℝ), (62122628513923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102307581/10000000000 : ℝ)|^41 ≤ (84217284671/25000000000000 : ℝ)^33
        have hw : |(-102307581/10000000000 : ℝ)|=(102307581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4544901281/10000000000 : ℝ)|^41 ≤ (300324018721/800000000000 : ℝ)^33
        have hw : |(-4544901281/10000000000 : ℝ)|=(4544901281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(852121129/1250000000 : ℝ)|^41 ≤ (62122628513923/100000000000000 : ℝ)^33
        have hw : |(852121129/1250000000 : ℝ)|=(852121129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_15 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (362773103/400000000 : ℝ)*x 0 + (1361013979/10000000000 : ℝ)*x 1 + (600522171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (362773103/400000000 : ℝ)^41 ≤ (44285368800811/50000000000000 : ℝ)^33 := by
    have hnat : (362773103 : ℕ)^41*50000000000000^33 ≤ 44285368800811^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362773103 400000000 44285368800811 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361013979/10000000000 : ℝ)^41 ≤ (8392471583411/100000000000000 : ℝ)^33 := by
    have hnat : (1361013979 : ℕ)^41*100000000000000^33 ≤ 8392471583411^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361013979 10000000000 8392471583411 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600522171/10000000000 : ℝ)^41 ≤ (189799425117/6250000000000 : ℝ)^33 := by
    have hnat : (600522171 : ℕ)^41*6250000000000^33 ≤ 189799425117^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600522171 10000000000 189799425117 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(362773103/400000000 : ℝ), (1361013979/10000000000 : ℝ), (600522171/10000000000 : ℝ)] ![(44285368800811/50000000000000 : ℝ), (8392471583411/100000000000000 : ℝ), (189799425117/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(362773103/400000000 : ℝ)|^41 ≤ (44285368800811/50000000000000 : ℝ)^33
        have hw : |(362773103/400000000 : ℝ)|=(362773103/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361013979/10000000000 : ℝ)|^41 ≤ (8392471583411/100000000000000 : ℝ)^33
        have hw : |(1361013979/10000000000 : ℝ)|=(1361013979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600522171/10000000000 : ℝ)|^41 ≤ (189799425117/6250000000000 : ℝ)^33
        have hw : |(600522171/10000000000 : ℝ)|=(600522171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_16 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (567937859/1000000000 : ℝ)*x 0 + (-4581111389/10000000000 : ℝ)*x 1 + (-1884271407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (567937859/1000000000 : ℝ)^41 ≤ (3094691767903/6250000000000 : ℝ)^33 := by
    have hnat : (567937859 : ℕ)^41*6250000000000^33 ≤ 3094691767903^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567937859 1000000000 3094691767903 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4581111389/10000000000 : ℝ)^41 ≤ (7582492037713/20000000000000 : ℝ)^33 := by
    have hnat : (4581111389 : ℕ)^41*20000000000000^33 ≤ 7582492037713^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4581111389 10000000000 7582492037713 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884271407/10000000000 : ℝ)^41 ≤ (12572471501707/100000000000000 : ℝ)^33 := by
    have hnat : (1884271407 : ℕ)^41*100000000000000^33 ≤ 12572471501707^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884271407 10000000000 12572471501707 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(567937859/1000000000 : ℝ), (-4581111389/10000000000 : ℝ), (-1884271407/10000000000 : ℝ)] ![(3094691767903/6250000000000 : ℝ), (7582492037713/20000000000000 : ℝ), (12572471501707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(567937859/1000000000 : ℝ)|^41 ≤ (3094691767903/6250000000000 : ℝ)^33
        have hw : |(567937859/1000000000 : ℝ)|=(567937859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4581111389/10000000000 : ℝ)|^41 ≤ (7582492037713/20000000000000 : ℝ)^33
        have hw : |(-4581111389/10000000000 : ℝ)|=(4581111389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1884271407/10000000000 : ℝ)|^41 ≤ (12572471501707/100000000000000 : ℝ)^33
        have hw : |(-1884271407/10000000000 : ℝ)|=(1884271407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_20 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (165458773/2000000000 : ℝ)*x 0 + (-190829081/2500000000 : ℝ)*x 1 + (1162594921/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165458773/2000000000 : ℝ)^41 ≤ (4521414279843/100000000000000 : ℝ)^33 := by
    have hnat : (165458773 : ℕ)^41*100000000000000^33 ≤ 4521414279843^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165458773 2000000000 4521414279843 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190829081/2500000000 : ℝ)^41 ≤ (4091146647931/100000000000000 : ℝ)^33 := by
    have hnat : (190829081 : ℕ)^41*100000000000000^33 ≤ 4091146647931^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190829081 2500000000 4091146647931 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1162594921/1250000000 : ℝ)^41 ≤ (91387439060251/100000000000000 : ℝ)^33 := by
    have hnat : (1162594921 : ℕ)^41*100000000000000^33 ≤ 91387439060251^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162594921 1250000000 91387439060251 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165458773/2000000000 : ℝ), (-190829081/2500000000 : ℝ), (1162594921/1250000000 : ℝ)] ![(4521414279843/100000000000000 : ℝ), (4091146647931/100000000000000 : ℝ), (91387439060251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165458773/2000000000 : ℝ)|^41 ≤ (4521414279843/100000000000000 : ℝ)^33
        have hw : |(165458773/2000000000 : ℝ)|=(165458773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-190829081/2500000000 : ℝ)|^41 ≤ (4091146647931/100000000000000 : ℝ)^33
        have hw : |(-190829081/2500000000 : ℝ)|=(190829081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1162594921/1250000000 : ℝ)|^41 ≤ (91387439060251/100000000000000 : ℝ)^33
        have hw : |(1162594921/1250000000 : ℝ)|=(1162594921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_21 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3744209/2000000000 : ℝ)*x 0 + (-8224184063/10000000000 : ℝ)*x 1 + (726154183/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3744209/2000000000 : ℝ)^41 ≤ (40839157581/100000000000000 : ℝ)^33 := by
    have hnat : (3744209 : ℕ)^41*100000000000000^33 ≤ 40839157581^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3744209 2000000000 40839157581 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8224184063/10000000000 : ℝ)^41 ≤ (4902180301647/6250000000000 : ℝ)^33 := by
    have hnat : (8224184063 : ℕ)^41*6250000000000^33 ≤ 4902180301647^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8224184063 10000000000 4902180301647 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (726154183/2500000000 : ℝ)^41 ≤ (21524276002429/100000000000000 : ℝ)^33 := by
    have hnat : (726154183 : ℕ)^41*100000000000000^33 ≤ 21524276002429^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726154183 2500000000 21524276002429 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3744209/2000000000 : ℝ), (-8224184063/10000000000 : ℝ), (726154183/2500000000 : ℝ)] ![(40839157581/100000000000000 : ℝ), (4902180301647/6250000000000 : ℝ), (21524276002429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3744209/2000000000 : ℝ)|^41 ≤ (40839157581/100000000000000 : ℝ)^33
        have hw : |(-3744209/2000000000 : ℝ)|=(3744209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8224184063/10000000000 : ℝ)|^41 ≤ (4902180301647/6250000000000 : ℝ)^33
        have hw : |(-8224184063/10000000000 : ℝ)|=(8224184063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(726154183/2500000000 : ℝ)|^41 ≤ (21524276002429/100000000000000 : ℝ)^33
        have hw : |(726154183/2500000000 : ℝ)|=(726154183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_22 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4224100003/5000000000 : ℝ)*x 0 + (1615715937/10000000000 : ℝ)*x 1 + (1377100999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224100003/5000000000 : ℝ)^41 ≤ (16219596507911/20000000000000 : ℝ)^33 := by
    have hnat : (4224100003 : ℕ)^41*20000000000000^33 ≤ 16219596507911^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224100003 5000000000 16219596507911 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1615715937/10000000000 : ℝ)^41 ≤ (1298265477299/12500000000000 : ℝ)^33 := by
    have hnat : (1615715937 : ℕ)^41*12500000000000^33 ≤ 1298265477299^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615715937 10000000000 1298265477299 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377100999/10000000000 : ℝ)^41 ≤ (4257946814627/50000000000000 : ℝ)^33 := by
    have hnat : (1377100999 : ℕ)^41*50000000000000^33 ≤ 4257946814627^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377100999 10000000000 4257946814627 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224100003/5000000000 : ℝ), (1615715937/10000000000 : ℝ), (1377100999/10000000000 : ℝ)] ![(16219596507911/20000000000000 : ℝ), (1298265477299/12500000000000 : ℝ), (4257946814627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224100003/5000000000 : ℝ)|^41 ≤ (16219596507911/20000000000000 : ℝ)^33
        have hw : |(4224100003/5000000000 : ℝ)|=(4224100003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1615715937/10000000000 : ℝ)|^41 ≤ (1298265477299/12500000000000 : ℝ)^33
        have hw : |(1615715937/10000000000 : ℝ)|=(1615715937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1377100999/10000000000 : ℝ)|^41 ≤ (4257946814627/50000000000000 : ℝ)^33
        have hw : |(1377100999/10000000000 : ℝ)|=(1377100999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_23 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2595422141/10000000000 : ℝ)*x 0 + (-376387913/625000000 : ℝ)*x 1 + (-3592489797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2595422141/10000000000 : ℝ)^41 ≤ (9357672226121/50000000000000 : ℝ)^33 := by
    have hnat : (2595422141 : ℕ)^41*50000000000000^33 ≤ 9357672226121^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595422141 10000000000 9357672226121 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376387913/625000000 : ℝ)^41 ≤ (53255330180717/100000000000000 : ℝ)^33 := by
    have hnat : (376387913 : ℕ)^41*100000000000000^33 ≤ 53255330180717^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376387913 625000000 53255330180717 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3592489797/10000000000 : ℝ)^41 ≤ (28029325358503/100000000000000 : ℝ)^33 := by
    have hnat : (3592489797 : ℕ)^41*100000000000000^33 ≤ 28029325358503^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3592489797 10000000000 28029325358503 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2595422141/10000000000 : ℝ), (-376387913/625000000 : ℝ), (-3592489797/10000000000 : ℝ)] ![(9357672226121/50000000000000 : ℝ), (53255330180717/100000000000000 : ℝ), (28029325358503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2595422141/10000000000 : ℝ)|^41 ≤ (9357672226121/50000000000000 : ℝ)^33
        have hw : |(2595422141/10000000000 : ℝ)|=(2595422141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-376387913/625000000 : ℝ)|^41 ≤ (53255330180717/100000000000000 : ℝ)^33
        have hw : |(-376387913/625000000 : ℝ)|=(376387913/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3592489797/10000000000 : ℝ)|^41 ≤ (28029325358503/100000000000000 : ℝ)^33
        have hw : |(-3592489797/10000000000 : ℝ)|=(3592489797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s0_27 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (127833471/250000000 : ℝ)*x 0 + (-11199557/2500000000 : ℝ)*x 1 + (788570849/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127833471/250000000 : ℝ)^41 ≤ (43459777574201/100000000000000 : ℝ)^33 := by
    have hnat : (127833471 : ℕ)^41*100000000000000^33 ≤ 43459777574201^33*250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127833471 250000000 43459777574201 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11199557/2500000000 : ℝ)^41 ≤ (6037255107/5000000000000 : ℝ)^33 := by
    have hnat : (11199557 : ℕ)^41*5000000000000^33 ≤ 6037255107^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11199557 2500000000 6037255107 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788570849/1250000000 : ℝ)^41 ≤ (56419477308467/100000000000000 : ℝ)^33 := by
    have hnat : (788570849 : ℕ)^41*100000000000000^33 ≤ 56419477308467^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788570849 1250000000 56419477308467 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(127833471/250000000 : ℝ), (-11199557/2500000000 : ℝ), (788570849/1250000000 : ℝ)] ![(43459777574201/100000000000000 : ℝ), (6037255107/5000000000000 : ℝ), (56419477308467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(127833471/250000000 : ℝ)|^41 ≤ (43459777574201/100000000000000 : ℝ)^33
        have hw : |(127833471/250000000 : ℝ)|=(127833471/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11199557/2500000000 : ℝ)|^41 ≤ (6037255107/5000000000000 : ℝ)^33
        have hw : |(-11199557/2500000000 : ℝ)|=(11199557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(788570849/1250000000 : ℝ)|^41 ≤ (56419477308467/100000000000000 : ℝ)^33
        have hw : |(788570849/1250000000 : ℝ)|=(788570849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s1_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1358866371/10000000000 : ℝ)*x 0 + (-2878142311/5000000000 : ℝ)*x 1 + (4905358823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1358866371/10000000000 : ℝ)^41 ≤ (1675204292333/20000000000000 : ℝ)^33 := by
    have hnat : (1358866371 : ℕ)^41*20000000000000^33 ≤ 1675204292333^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358866371 10000000000 1675204292333 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2878142311/5000000000 : ℝ)^41 ≤ (10069894587617/20000000000000 : ℝ)^33 := by
    have hnat : (2878142311 : ℕ)^41*20000000000000^33 ≤ 10069894587617^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2878142311 5000000000 10069894587617 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4905358823/10000000000 : ℝ)^41 ≤ (41274505580041/100000000000000 : ℝ)^33 := by
    have hnat : (4905358823 : ℕ)^41*100000000000000^33 ≤ 41274505580041^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4905358823 10000000000 41274505580041 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1358866371/10000000000 : ℝ), (-2878142311/5000000000 : ℝ), (4905358823/10000000000 : ℝ)] ![(1675204292333/20000000000000 : ℝ), (10069894587617/20000000000000 : ℝ), (41274505580041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1358866371/10000000000 : ℝ)|^41 ≤ (1675204292333/20000000000000 : ℝ)^33
        have hw : |(-1358866371/10000000000 : ℝ)|=(1358866371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2878142311/5000000000 : ℝ)|^41 ≤ (10069894587617/20000000000000 : ℝ)^33
        have hw : |(-2878142311/5000000000 : ℝ)|=(2878142311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4905358823/10000000000 : ℝ)|^41 ≤ (41274505580041/100000000000000 : ℝ)^33
        have hw : |(4905358823/10000000000 : ℝ)|=(4905358823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s1_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6202556139/10000000000 : ℝ)*x 0 + (3075843173/10000000000 : ℝ)*x 1 + (1458818191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6202556139/10000000000 : ℝ)^41 ≤ (55243961475077/100000000000000 : ℝ)^33 := by
    have hnat : (6202556139 : ℕ)^41*100000000000000^33 ≤ 55243961475077^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6202556139 10000000000 55243961475077 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3075843173/10000000000 : ℝ)^41 ≤ (23111827891637/100000000000000 : ℝ)^33 := by
    have hnat : (3075843173 : ℕ)^41*100000000000000^33 ≤ 23111827891637^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3075843173 10000000000 23111827891637 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1458818191/5000000000 : ℝ)^41 ≤ (5411052656383/25000000000000 : ℝ)^33 := by
    have hnat : (1458818191 : ℕ)^41*25000000000000^33 ≤ 5411052656383^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458818191 5000000000 5411052656383 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6202556139/10000000000 : ℝ), (3075843173/10000000000 : ℝ), (1458818191/5000000000 : ℝ)] ![(55243961475077/100000000000000 : ℝ), (23111827891637/100000000000000 : ℝ), (5411052656383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6202556139/10000000000 : ℝ)|^41 ≤ (55243961475077/100000000000000 : ℝ)^33
        have hw : |(6202556139/10000000000 : ℝ)|=(6202556139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3075843173/10000000000 : ℝ)|^41 ≤ (23111827891637/100000000000000 : ℝ)^33
        have hw : |(3075843173/10000000000 : ℝ)|=(3075843173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1458818191/5000000000 : ℝ)|^41 ≤ (5411052656383/25000000000000 : ℝ)^33
        have hw : |(1458818191/5000000000 : ℝ)|=(1458818191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s1_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2455979303/5000000000 : ℝ)*x 0 + (-1920558897/5000000000 : ℝ)*x 1 + (-3609795439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2455979303/5000000000 : ℝ)^41 ≤ (8268702144829/20000000000000 : ℝ)^33 := by
    have hnat : (2455979303 : ℕ)^41*20000000000000^33 ≤ 8268702144829^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2455979303 5000000000 8268702144829 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1920558897/5000000000 : ℝ)^41 ≤ (15229655682201/50000000000000 : ℝ)^33 := by
    have hnat : (1920558897 : ℕ)^41*50000000000000^33 ≤ 15229655682201^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920558897 5000000000 15229655682201 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3609795439/10000000000 : ℝ)^41 ≤ (7049294476439/25000000000000 : ℝ)^33 := by
    have hnat : (3609795439 : ℕ)^41*25000000000000^33 ≤ 7049294476439^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3609795439 10000000000 7049294476439 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2455979303/5000000000 : ℝ), (-1920558897/5000000000 : ℝ), (-3609795439/10000000000 : ℝ)] ![(8268702144829/20000000000000 : ℝ), (15229655682201/50000000000000 : ℝ), (7049294476439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2455979303/5000000000 : ℝ)|^41 ≤ (8268702144829/20000000000000 : ℝ)^33
        have hw : |(2455979303/5000000000 : ℝ)|=(2455979303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1920558897/5000000000 : ℝ)|^41 ≤ (15229655682201/50000000000000 : ℝ)^33
        have hw : |(-1920558897/5000000000 : ℝ)|=(1920558897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3609795439/10000000000 : ℝ)|^41 ≤ (7049294476439/25000000000000 : ℝ)^33
        have hw : |(-3609795439/10000000000 : ℝ)|=(3609795439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321075_s1_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3282963313/10000000000 : ℝ)*x 0 + (-170347157/625000000 : ℝ)*x 1 + (6185100941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3282963313/10000000000 : ℝ)^41 ≤ (25060930275377/100000000000000 : ℝ)^33 := by
    have hnat : (3282963313 : ℕ)^41*100000000000000^33 ≤ 25060930275377^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3282963313 10000000000 25060930275377 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170347157/625000000 : ℝ)^41 ≤ (19888198578327/100000000000000 : ℝ)^33 := by
    have hnat : (170347157 : ℕ)^41*100000000000000^33 ≤ 19888198578327^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170347157 625000000 19888198578327 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6185100941/10000000000 : ℝ)^41 ≤ (172033972319/312500000000 : ℝ)^33 := by
    have hnat : (6185100941 : ℕ)^41*312500000000^33 ≤ 172033972319^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6185100941 10000000000 172033972319 312500000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3282963313/10000000000 : ℝ), (-170347157/625000000 : ℝ), (6185100941/10000000000 : ℝ)] ![(25060930275377/100000000000000 : ℝ), (19888198578327/100000000000000 : ℝ), (172033972319/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3282963313/10000000000 : ℝ)|^41 ≤ (25060930275377/100000000000000 : ℝ)^33
        have hw : |(3282963313/10000000000 : ℝ)|=(3282963313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-170347157/625000000 : ℝ)|^41 ≤ (19888198578327/100000000000000 : ℝ)^33
        have hw : |(-170347157/625000000 : ℝ)|=(170347157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6185100941/10000000000 : ℝ)|^41 ≤ (172033972319/312500000000 : ℝ)^33
        have hw : |(6185100941/10000000000 : ℝ)|=(6185100941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321075 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (168549/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-9604303/1000000000 : ℝ)*X 0 0+(-859696503/1250000000 : ℝ)*X 0 1+(896066927/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5535292427/10000000000 : ℝ)*X 2 0+(-1753698317/5000000000 : ℝ)*X 2 1+(-325901381/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-79352769/2000000000 : ℝ)*X 0 0+(-207456471/250000000 : ℝ)*X 0 1+(2612874991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((584532439/1000000000 : ℝ)*X 1 0+(4148789417/10000000000 : ℝ)*X 1 1+(2190795323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1163723911/2000000000 : ℝ)*X 2 0+(-143474637/400000000 : ℝ)*X 2 1+(-2847252717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((223741449/2000000000 : ℝ)*X 0 0+(-177073/500000000 : ℝ)*X 0 1+(189332597/200000000 : ℝ)*X 0 2+(223741449/2000000000 : ℝ)*X 1 0+(-177073/500000000 : ℝ)*X 1 1+(189332597/200000000 : ℝ)*X 1 2+(223741449/2000000000 : ℝ)*X 2 0+(-177073/500000000 : ℝ)*X 2 1+(189332597/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-102307581/10000000000 : ℝ)*X 0 0+(-4544901281/10000000000 : ℝ)*X 0 1+(852121129/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((362773103/400000000 : ℝ)*X 1 0+(1361013979/10000000000 : ℝ)*X 1 1+(600522171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((567937859/1000000000 : ℝ)*X 2 0+(-4581111389/10000000000 : ℝ)*X 2 1+(-1884271407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((165458773/2000000000 : ℝ)*X 0 0+(-190829081/2500000000 : ℝ)*X 0 1+(1162594921/1250000000 : ℝ)*X 0 2+(165458773/2000000000 : ℝ)*X 1 0+(-190829081/2500000000 : ℝ)*X 1 1+(1162594921/1250000000 : ℝ)*X 1 2+(165458773/2000000000 : ℝ)*X 2 0+(-190829081/2500000000 : ℝ)*X 2 1+(1162594921/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-3744209/2000000000 : ℝ)*X 0 0+(-8224184063/10000000000 : ℝ)*X 0 1+(726154183/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4224100003/5000000000 : ℝ)*X 1 0+(1615715937/10000000000 : ℝ)*X 1 1+(1377100999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2595422141/10000000000 : ℝ)*X 2 0+(-376387913/625000000 : ℝ)*X 2 1+(-3592489797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((127833471/250000000 : ℝ)*X 0 0+(-11199557/2500000000 : ℝ)*X 0 1+(788570849/1250000000 : ℝ)*X 0 2+(127833471/250000000 : ℝ)*X 1 0+(-11199557/2500000000 : ℝ)*X 1 1+(788570849/1250000000 : ℝ)*X 1 2+(127833471/250000000 : ℝ)*X 2 0+(-11199557/2500000000 : ℝ)*X 2 1+(788570849/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((11973/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11973/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1488649168353481321689/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (664290060047/1000000000000 : ℝ)*(base7) + (67471183403/1000000000000 : ℝ)*(base43) + (628939948919/1000000000000 : ℝ)*(base54) + (32533474571/1000000000000 : ℝ)*(base59) + (1054815363679/500000000000 : ℝ)*(major_s0_0) + (408431908791/200000000000 : ℝ)*(major_s0_1) + (1480690778439/1000000000000 : ℝ)*(major_s0_2) + (1448499/1000000000000 : ℝ)*(sp_s0_0) + (19178919/31250000000 : ℝ)*(sp_s0_2) + (1335134901357/500000000000 : ℝ)*(sp_s0_7) + (85555020967/31250000000 : ℝ)*(sp_s0_8) + (1020367906607/500000000000 : ℝ)*(sp_s0_9) + (571814420361/500000000000 : ℝ)*(sp_s0_13) + (2279541/125000000000 : ℝ)*(sp_s0_21) + (554139364797/500000000000 : ℝ)*(f.failure) + (85555020967/31250000000 : ℝ)*(f.sum) + (532220421006807/10000000000000000000000000000 : ℝ)*base63 + (3272704609078507/5000000000000000000000000000 : ℝ)*base64 + (1721300482302453/2000000000000000000000000000 : ℝ)*base67 + (5467994008721637/10000000000000000000000000000 : ℝ)*base69 + (15635218959799/100000000000000000000000000 : ℝ)*base70 + (2255609191094627/2500000000000000000000000000 : ℝ)*base73 + (416847631628517/1000000000000000000000000000 : ℝ)*base75 + (1988222443911443/5000000000000000000000000000 : ℝ)*base76 + (5444801240890773/10000000000000000000000000000 : ℝ)*base79 + (3841/3125000000000000 : ℝ)*base86 + (3841/3125000000000000 : ℝ)*base88 + (3841/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-35009/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-35009/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (612423335196739809747/39062500000000000000000000 : ℝ) := by norm_num
    linear_combination (430085190389/500000000000 : ℝ)*(base7) + (13540803/500000000000 : ℝ)*(base31) + (276581487643/500000000000 : ℝ)*(base33) + (3248797/500000000000 : ℝ)*(base40) + (41427071657/1000000000000 : ℝ)*(base60) + (24297865039/25000000000 : ℝ)*(major_s0_0) + (762538788423/500000000000 : ℝ)*(major_s0_1) + (762538788423/500000000000 : ℝ)*(major_s0_2) + (18185163/250000000000 : ℝ)*(sp_s0_9) + (353138460031/200000000000 : ℝ)*(sp_s0_14) + (1212513530113/1000000000000 : ℝ)*(sp_s0_15) + (151557073027/125000000000 : ℝ)*(sp_s0_16) + (1661331401659/1000000000000 : ℝ)*(sp_s0_20) + (3948689/250000000000 : ℝ)*(sp_s0_22) + (801188102487/1000000000000 : ℝ)*(f.failure) + (353138460031/200000000000 : ℝ)*(f.sum) + (2610842359735311/5000000000000000000000000000 : ℝ)*base63 + (1788286790768901/2500000000000000000000000000 : ℝ)*base65 + (180663432302491/5000000000000000000000000000 : ℝ)*base66 + (1569104030697509/5000000000000000000000000000 : ℝ)*base69 + (2048011154163271/2500000000000000000000000000 : ℝ)*base71 + (49575785063193/125000000000000000000000000 : ℝ)*base72 + (1336814939268901/2500000000000000000000000000 : ℝ)*base75 + (71181816189437/250000000000000000000000000 : ℝ)*base77 + (1794869117330211/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (339/6250000000000000 : ℝ)*base87 + (339/6250000000000000 : ℝ)*base89 + (339/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66273/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(66273/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28331882145877541285853/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81700214951/125000000000 : ℝ)*(base7) + (359973411019/1000000000000 : ℝ)*(base33) + (394837925639/1000000000000 : ℝ)*(base40) + (5791423/1000000000000 : ℝ)*(base43) + (63852949349/500000000000 : ℝ)*(base49) + (849053/1000000000000 : ℝ)*(base59) + (214243066787/100000000000 : ℝ)*(major_s0_0) + (1251199143733/500000000000 : ℝ)*(major_s0_1) + (312800509861/125000000000 : ℝ)*(major_s0_2) + (36211/3906250000 : ℝ)*(sp_s0_0) + (1661478495719/500000000000 : ℝ)*(sp_s0_21) + (1481499320929/500000000000 : ℝ)*(sp_s0_22) + (592598570087/200000000000 : ℝ)*(sp_s0_23) + (1968220992791/1000000000000 : ℝ)*(sp_s0_27) + (1314619273183/1000000000000 : ℝ)*(f.failure) + (830743013219/250000000000 : ℝ)*(f.sum) + (339460925942397/2500000000000000000000000000 : ℝ)*base63 + (179611433845607/625000000000000000000000000 : ℝ)*base65 + (2973533912163761/5000000000000000000000000000 : ℝ)*base66 + (204159057652737/1250000000000000000000000000 : ℝ)*base68 + (1517478333029461/5000000000000000000000000000 : ℝ)*base71 + (282075650831369/500000000000000000000000000 : ℝ)*base72 + (1190670012997871/2500000000000000000000000000 : ℝ)*base75 + (313200152347079/1000000000000000000000000000 : ℝ)*base76 + (1043855877977451/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1901/6250000000000000 : ℝ)*base87 + (1901/6250000000000000 : ℝ)*base89 + (8151/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (11973/20000 : ℝ) ^ (81/16 : ℝ) ≤ (7446260849229178039/100000000000000000000 : ℝ) := by
    have hpowers : (11973/20000 : ℝ)^81 ≤ (7446260849229178039/100000000000000000000 : ℝ)^16 := by
      have hnat : (11973 : ℕ)^81*100000000000000000000^16 ≤ 7446260849229178039^16*20000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11973 20000 7446260849229178039 100000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11973/20000 : ℝ)) (X := (7446260849229178039/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (107446260849229178039/100000000000000000000 : ℝ) ≤ (1267859878392349/1250000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (107446260849229178039/100000000000000000000 : ℝ)^16 ≤ (1267859878392349/1250000000000000 : ℝ)^81 := by
      have hnat : (107446260849229178039 : ℕ)^16*1250000000000000^81 ≤ 1267859878392349^81*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107446260849229178039 100000000000000000000 1267859878392349 1250000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1267859878392349/1250000000000000 : ℝ)) (X := (107446260849229178039/100000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (57446260849229178039/50000000000000000000 : ℝ) ≤ (1284752574918209/1250000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (57446260849229178039/50000000000000000000 : ℝ)^16 ≤ (1284752574918209/1250000000000000 : ℝ)^81 := by
      have hnat : (57446260849229178039 : ℕ)^16*1250000000000000^81 ≤ 1284752574918209^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57446260849229178039 50000000000000000000 1284752574918209 1250000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1284752574918209/1250000000000000 : ℝ)) (X := (57446260849229178039/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(17859878392349/748312500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(844634826293/37415625000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (11973/20000 : ℝ)) (alpha := (17859878392349/748312500000000 : ℝ)) (beta := (844634826293/37415625000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11973/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(17859878392349/748312500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(844634826293/37415625000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (35009/50000 : ℝ) ^ (81/16 : ℝ) ≤ (16457888406666758413/100000000000000000000 : ℝ) := by
    have hpowers : (35009/50000 : ℝ)^81 ≤ (16457888406666758413/100000000000000000000 : ℝ)^16 := by
      have hnat : (35009 : ℕ)^81*100000000000000000000^16 ≤ 16457888406666758413^16*50000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35009 50000 16457888406666758413 100000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35009/50000 : ℝ)) (X := (16457888406666758413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (116457888406666758413/100000000000000000000 : ℝ) ≤ (2061106333830651/2000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (116457888406666758413/100000000000000000000 : ℝ)^16 ≤ (2061106333830651/2000000000000000 : ℝ)^81 := by
      have hnat : (116457888406666758413 : ℕ)^16*2000000000000000^81 ≤ 2061106333830651^81*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116457888406666758413 100000000000000000000 2061106333830651 2000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2061106333830651/2000000000000000 : ℝ)) (X := (116457888406666758413/100000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (66457888406666758413/50000000000000000000 : ℝ) ≤ (528908058290091/500000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (66457888406666758413/50000000000000000000 : ℝ)^16 ≤ (528908058290091/500000000000000 : ℝ)^81 := by
      have hnat : (66457888406666758413 : ℕ)^16*500000000000000^81 ≤ 528908058290091^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66457888406666758413 50000000000000000000 528908058290091 500000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (528908058290091/500000000000000 : ℝ)) (X := (66457888406666758413/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(61106333830651/1400360000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(54525899329713/1400360000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (35009/50000 : ℝ)) (alpha := (61106333830651/1400360000000000 : ℝ)) (beta := (54525899329713/1400360000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (35009/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(61106333830651/1400360000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(54525899329713/1400360000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (66273/100000 : ℝ) ^ (81/16 : ℝ) ≤ (12459961238328767467/100000000000000000000 : ℝ) := by
    have hpowers : (66273/100000 : ℝ)^81 ≤ (12459961238328767467/100000000000000000000 : ℝ)^16 := by
      have hnat : (66273 : ℕ)^81*100000000000000000000^16 ≤ 12459961238328767467^16*100000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66273 100000 12459961238328767467 100000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66273/100000 : ℝ)) (X := (12459961238328767467/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (112459961238328767467/100000000000000000000 : ℝ) ≤ (2558666445213267/2500000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (112459961238328767467/100000000000000000000 : ℝ)^16 ≤ (2558666445213267/2500000000000000 : ℝ)^81 := by
      have hnat : (112459961238328767467 : ℕ)^16*2500000000000000^81 ≤ 2558666445213267^81*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112459961238328767467 100000000000000000000 2558666445213267 2500000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2558666445213267/2500000000000000 : ℝ)) (X := (112459961238328767467/100000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (62459961238328767467/50000000000000000000 : ℝ) ≤ (10449313147263281/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (62459961238328767467/50000000000000000000 : ℝ)^16 ≤ (10449313147263281/10000000000000000 : ℝ)^81 := by
      have hnat : (62459961238328767467 : ℕ)^16*10000000000000000^81 ≤ 10449313147263281^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62459961238328767467 50000000000000000000 10449313147263281 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10449313147263281/10000000000000000 : ℝ)) (X := (62459961238328767467/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(58666445213267/1656825000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(214647366410213/6627300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (66273/100000 : ℝ)) (alpha := (58666445213267/1656825000000000 : ℝ)) (beta := (214647366410213/6627300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (66273/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(58666445213267/1656825000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(214647366410213/6627300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1358866371/10000000000 : ℝ)*X 0 0+(-2878142311/5000000000 : ℝ)*X 0 1+(4905358823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6202556139/10000000000 : ℝ)*X 1 0+(3075843173/10000000000 : ℝ)*X 1 1+(1458818191/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2455979303/5000000000 : ℝ)*X 2 0+(-1920558897/5000000000 : ℝ)*X 2 1+(-3609795439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3282963313/10000000000 : ℝ)*X 0 0+(-170347157/625000000 : ℝ)*X 0 1+(6185100941/10000000000 : ℝ)*X 0 2+(3282963313/10000000000 : ℝ)*X 1 0+(-170347157/625000000 : ℝ)*X 1 1+(6185100941/10000000000 : ℝ)*X 1 2+(3282963313/10000000000 : ℝ)*X 2 0+(-170347157/625000000 : ℝ)*X 2 1+(6185100941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321075_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-26316/3125 : ℝ) < ((-11897/6250 : ℝ)*P 0+(-11897/6250 : ℝ)*P 1+(-11897/6250 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-26316/3125 : ℝ) < (-36883031003380449288330323977391/4408259050000000000000000000000 : ℝ) := by norm_num
    linear_combination (54781/1000000000000 : ℝ)*(base10) + (30961/1000000000000 : ℝ)*(base19) + (28181/500000000000 : ℝ)*(base21) + (13097/500000000000 : ℝ)*(base31) + (51427112071/100000000000 : ℝ)*(base40) + (65596678643/500000000000 : ℝ)*(base49) + (2159/62500000000 : ℝ)*(base54) + (87226623037/1000000000000 : ℝ)*(base60) + (11897/6250 : ℝ)*(major_s1_0) + (11897/6250 : ℝ)*(major_s1_1) + (118969997841/62500000000 : ℝ)*(major_s1_2) + (2788933972991/1000000000000 : ℝ)*(sp_s1_0) + (2788933996811/1000000000000 : ℝ)*(sp_s1_1) + (2788933936867/1000000000000 : ℝ)*(sp_s1_2) + (499999969631/500000000000 : ℝ)*(sp_s1_6) + (697233506943/250000000000 : ℝ)*(f.sum) + (10299336017209865737/38669190950000000000000000000000 : ℝ)*base63 + (193928517427629/552275000000000000000000000 : ℝ)*base64 + (9245922216243/70018000000000000000000000 : ℝ)*base66 + (459908288433743/1104550000000000000000000000 : ℝ)*base69 + (3061601065186768109/13224777150000000000000000000000 : ℝ)*base70 + (762941043893/7483125000000000000000000 : ℝ)*base73 + (12964685610209/43761250000000000000000000 : ℝ)*base74 + (18273633228817/59865000000000000000000000 : ℝ)*base76 + (68993054441929519/322432890000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p021_b041 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 75 ≤ c.val) (hhi : c.val < 76)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=75 := by omega
  rcases hc with rfl
  · exact collision_c321075 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 75 ≤ c.val) (hhi : c.val < 76)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p021_b041 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
