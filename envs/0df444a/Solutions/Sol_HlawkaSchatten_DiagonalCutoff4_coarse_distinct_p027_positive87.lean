-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_positive87
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:16:20.662048+00:00
-- url     : https://prove2.me/submissions/54059d31-4ebd-40cf-9ceb-b099c0b2ef87

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
namespace HlawkaSchatten.DiagonalCutoff4
theorem positive_chart_nonnegative {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    {orders : Fin 3 → Fin 3 → Fin 3}
    (hX : OrderedChart p k A d X orders (fun _ _ => true)) :
    ∀ i h, 0 ≤ pair X i h := by
  intro i h
  obtain ⟨j,rfl⟩ := (hX.permutation i).2 h
  have hh := hX.ordered i
  simp only [signedPair,signValue,Bool.true_eq,if_true,one_mul] at hh
  fin_cases j
  · exact (hh.1.trans hh.2.1).trans hh.2.2
  · exact hh.1.trans hh.2.1
  · exact hh.1
theorem positive_chart_tailratio {p k A d rho : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    {orders : Fin 3 → Fin 3 → Fin 3}
    (hX : OrderedChart p k A d X orders (fun _ _ => true))
    (hm : ∀ i, orders i 0=i)
    (hbig : ∀ i, pair X i (orders i 1) ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i := by
  intro i h hih
  rw [abs_of_nonneg (positive_chart_nonnegative hX i h)]
  obtain ⟨j,rfl⟩ := (hX.permutation i).2 h
  have hh := hX.ordered i
  simp only [signedPair,signValue,Bool.true_eq,if_true,one_mul] at hh
  fin_cases j
  · exact (hih (hm i).symm).elim
  · exact hbig i
  · exact hh.2.1.trans (hbig i)
end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c327087_s0_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-92991719/5000000000 : ℝ)*x 0 + (5457472651/10000000000 : ℝ)*x 1 + (1440919367/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92991719/5000000000 : ℝ)^91 ≤ (12419824973/1562500000000 : ℝ)^75 := by
    have hnat : (92991719 : ℕ)^91*1562500000000^75 ≤ 12419824973^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92991719 5000000000 12419824973 1562500000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457472651/10000000000 : ℝ)^91 ≤ (2997527111803/6250000000000 : ℝ)^75 := by
    have hnat : (5457472651 : ℕ)^91*6250000000000^75 ≤ 2997527111803^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457472651 10000000000 2997527111803 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1440919367/2500000000 : ℝ)^91 ≤ (51244697390213/100000000000000 : ℝ)^75 := by
    have hnat : (1440919367 : ℕ)^91*100000000000000^75 ≤ 51244697390213^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440919367 2500000000 51244697390213 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92991719/5000000000 : ℝ), (5457472651/10000000000 : ℝ), (1440919367/2500000000 : ℝ)] ![(12419824973/1562500000000 : ℝ), (2997527111803/6250000000000 : ℝ), (51244697390213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92991719/5000000000 : ℝ)|^91 ≤ (12419824973/1562500000000 : ℝ)^75
        have hw : |(-92991719/5000000000 : ℝ)|=(92991719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457472651/10000000000 : ℝ)|^91 ≤ (2997527111803/6250000000000 : ℝ)^75
        have hw : |(5457472651/10000000000 : ℝ)|=(5457472651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1440919367/2500000000 : ℝ)|^91 ≤ (51244697390213/100000000000000 : ℝ)^75
        have hw : |(1440919367/2500000000 : ℝ)|=(1440919367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1440919367/2500000000 : ℝ)*x 0 + (-92991719/5000000000 : ℝ)*x 1 + (5457472651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1440919367/2500000000 : ℝ)^91 ≤ (51244697390213/100000000000000 : ℝ)^75 := by
    have hnat : (1440919367 : ℕ)^91*100000000000000^75 ≤ 51244697390213^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440919367 2500000000 51244697390213 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92991719/5000000000 : ℝ)^91 ≤ (12419824973/1562500000000 : ℝ)^75 := by
    have hnat : (92991719 : ℕ)^91*1562500000000^75 ≤ 12419824973^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92991719 5000000000 12419824973 1562500000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457472651/10000000000 : ℝ)^91 ≤ (2997527111803/6250000000000 : ℝ)^75 := by
    have hnat : (5457472651 : ℕ)^91*6250000000000^75 ≤ 2997527111803^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457472651 10000000000 2997527111803 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1440919367/2500000000 : ℝ), (-92991719/5000000000 : ℝ), (5457472651/10000000000 : ℝ)] ![(51244697390213/100000000000000 : ℝ), (12419824973/1562500000000 : ℝ), (2997527111803/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1440919367/2500000000 : ℝ)|^91 ≤ (51244697390213/100000000000000 : ℝ)^75
        have hw : |(1440919367/2500000000 : ℝ)|=(1440919367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92991719/5000000000 : ℝ)|^91 ≤ (12419824973/1562500000000 : ℝ)^75
        have hw : |(-92991719/5000000000 : ℝ)|=(92991719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457472651/10000000000 : ℝ)|^91 ≤ (2997527111803/6250000000000 : ℝ)^75
        have hw : |(5457472651/10000000000 : ℝ)|=(5457472651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5457472651/10000000000 : ℝ)*x 0 + (1440919367/2500000000 : ℝ)*x 1 + (-92991719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5457472651/10000000000 : ℝ)^91 ≤ (2997527111803/6250000000000 : ℝ)^75 := by
    have hnat : (5457472651 : ℕ)^91*6250000000000^75 ≤ 2997527111803^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457472651 10000000000 2997527111803 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1440919367/2500000000 : ℝ)^91 ≤ (51244697390213/100000000000000 : ℝ)^75 := by
    have hnat : (1440919367 : ℕ)^91*100000000000000^75 ≤ 51244697390213^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440919367 2500000000 51244697390213 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92991719/5000000000 : ℝ)^91 ≤ (12419824973/1562500000000 : ℝ)^75 := by
    have hnat : (92991719 : ℕ)^91*1562500000000^75 ≤ 12419824973^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92991719 5000000000 12419824973 1562500000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5457472651/10000000000 : ℝ), (1440919367/2500000000 : ℝ), (-92991719/5000000000 : ℝ)] ![(2997527111803/6250000000000 : ℝ), (51244697390213/100000000000000 : ℝ), (12419824973/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5457472651/10000000000 : ℝ)|^91 ≤ (2997527111803/6250000000000 : ℝ)^75
        have hw : |(5457472651/10000000000 : ℝ)|=(5457472651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1440919367/2500000000 : ℝ)|^91 ≤ (51244697390213/100000000000000 : ℝ)^75
        have hw : |(1440919367/2500000000 : ℝ)|=(1440919367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-92991719/5000000000 : ℝ)|^91 ≤ (12419824973/1562500000000 : ℝ)^75
        have hw : |(-92991719/5000000000 : ℝ)|=(92991719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-46832271/312500000 : ℝ)*x 0 + (124246861/1250000000 : ℝ)*x 1 + (4327751193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46832271/312500000 : ℝ)^91 ≤ (9996397220859/100000000000000 : ℝ)^75 := by
    have hnat : (46832271 : ℕ)^91*100000000000000^75 ≤ 9996397220859^75*312500000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46832271 312500000 9996397220859 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124246861/1250000000 : ℝ)^91 ≤ (6074103209743/100000000000000 : ℝ)^75 := by
    have hnat : (124246861 : ℕ)^91*100000000000000^75 ≤ 6074103209743^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124246861 1250000000 6074103209743 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4327751193/5000000000 : ℝ)^91 ≤ (83929499560491/100000000000000 : ℝ)^75 := by
    have hnat : (4327751193 : ℕ)^91*100000000000000^75 ≤ 83929499560491^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327751193 5000000000 83929499560491 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46832271/312500000 : ℝ), (124246861/1250000000 : ℝ), (4327751193/5000000000 : ℝ)] ![(9996397220859/100000000000000 : ℝ), (6074103209743/100000000000000 : ℝ), (83929499560491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46832271/312500000 : ℝ)|^91 ≤ (9996397220859/100000000000000 : ℝ)^75
        have hw : |(-46832271/312500000 : ℝ)|=(46832271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124246861/1250000000 : ℝ)|^91 ≤ (6074103209743/100000000000000 : ℝ)^75
        have hw : |(124246861/1250000000 : ℝ)|=(124246861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4327751193/5000000000 : ℝ)|^91 ≤ (83929499560491/100000000000000 : ℝ)^75
        have hw : |(4327751193/5000000000 : ℝ)|=(4327751193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (65910261/156250000 : ℝ)*x 0 + (-10431569/400000000 : ℝ)*x 1 + (3448452561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65910261/156250000 : ℝ)^91 ≤ (1754411171927/5000000000000 : ℝ)^75 := by
    have hnat : (65910261 : ℕ)^91*5000000000000^75 ≤ 1754411171927^75*156250000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65910261 156250000 1754411171927 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10431569/400000000 : ℝ)^91 ≤ (239585996261/20000000000000 : ℝ)^75 := by
    have hnat : (10431569 : ℕ)^91*20000000000000^75 ≤ 239585996261^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10431569 400000000 239585996261 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3448452561/5000000000 : ℝ)^91 ≤ (6371384656017/10000000000000 : ℝ)^75 := by
    have hnat : (3448452561 : ℕ)^91*10000000000000^75 ≤ 6371384656017^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448452561 5000000000 6371384656017 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65910261/156250000 : ℝ), (-10431569/400000000 : ℝ), (3448452561/5000000000 : ℝ)] ![(1754411171927/5000000000000 : ℝ), (239585996261/20000000000000 : ℝ), (6371384656017/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65910261/156250000 : ℝ)|^91 ≤ (1754411171927/5000000000000 : ℝ)^75
        have hw : |(65910261/156250000 : ℝ)|=(65910261/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10431569/400000000 : ℝ)|^91 ≤ (239585996261/20000000000000 : ℝ)^75
        have hw : |(-10431569/400000000 : ℝ)|=(10431569/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3448452561/5000000000 : ℝ)|^91 ≤ (6371384656017/10000000000000 : ℝ)^75
        have hw : |(3448452561/5000000000 : ℝ)|=(3448452561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (43272801/200000000 : ℝ)*x 0 + (8694219913/10000000000 : ℝ)*x 1 + (-3487363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43272801/200000000 : ℝ)^91 ≤ (39020948613/250000000000 : ℝ)^75 := by
    have hnat : (43272801 : ℕ)^91*250000000000^75 ≤ 39020948613^75*200000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43272801 200000000 39020948613 250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8694219913/10000000000 : ℝ)^91 ≤ (42192619712307/50000000000000 : ℝ)^75 := by
    have hnat : (8694219913 : ℕ)^91*50000000000000^75 ≤ 42192619712307^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8694219913 10000000000 42192619712307 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3487363/10000000000 : ℝ)^91 ≤ (1276222933/20000000000000 : ℝ)^75 := by
    have hnat : (3487363 : ℕ)^91*20000000000000^75 ≤ 1276222933^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3487363 10000000000 1276222933 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43272801/200000000 : ℝ), (8694219913/10000000000 : ℝ), (-3487363/10000000000 : ℝ)] ![(39020948613/250000000000 : ℝ), (42192619712307/50000000000000 : ℝ), (1276222933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43272801/200000000 : ℝ)|^91 ≤ (39020948613/250000000000 : ℝ)^75
        have hw : |(43272801/200000000 : ℝ)|=(43272801/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8694219913/10000000000 : ℝ)|^91 ≤ (42192619712307/50000000000000 : ℝ)^75
        have hw : |(8694219913/10000000000 : ℝ)|=(8694219913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3487363/10000000000 : ℝ)|^91 ≤ (1276222933/20000000000000 : ℝ)^75
        have hw : |(-3487363/10000000000 : ℝ)|=(3487363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (250695877/1250000000 : ℝ)*x 0 + (7072784033/10000000000 : ℝ)*x 1 + (332775727/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250695877/1250000000 : ℝ)^91 ≤ (14235774825201/100000000000000 : ℝ)^75 := by
    have hnat : (250695877 : ℕ)^91*100000000000000^75 ≤ 14235774825201^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250695877 1250000000 14235774825201 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7072784033/10000000000 : ℝ)^91 ≤ (65690567717389/100000000000000 : ℝ)^75 := by
    have hnat : (7072784033 : ℕ)^91*100000000000000^75 ≤ 65690567717389^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7072784033 10000000000 65690567717389 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (332775727/1250000000 : ℝ)^91 ≤ (20073657436489/100000000000000 : ℝ)^75 := by
    have hnat : (332775727 : ℕ)^91*100000000000000^75 ≤ 20073657436489^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332775727 1250000000 20073657436489 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(250695877/1250000000 : ℝ), (7072784033/10000000000 : ℝ), (332775727/1250000000 : ℝ)] ![(14235774825201/100000000000000 : ℝ), (65690567717389/100000000000000 : ℝ), (20073657436489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(250695877/1250000000 : ℝ)|^91 ≤ (14235774825201/100000000000000 : ℝ)^75
        have hw : |(250695877/1250000000 : ℝ)|=(250695877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7072784033/10000000000 : ℝ)|^91 ≤ (65690567717389/100000000000000 : ℝ)^75
        have hw : |(7072784033/10000000000 : ℝ)|=(7072784033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(332775727/1250000000 : ℝ)|^91 ≤ (20073657436489/100000000000000 : ℝ)^75
        have hw : |(332775727/1250000000 : ℝ)|=(332775727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3487363/10000000000 : ℝ)*x 0 + (43272801/200000000 : ℝ)*x 1 + (8694219913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3487363/10000000000 : ℝ)^91 ≤ (1276222933/20000000000000 : ℝ)^75 := by
    have hnat : (3487363 : ℕ)^91*20000000000000^75 ≤ 1276222933^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3487363 10000000000 1276222933 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43272801/200000000 : ℝ)^91 ≤ (39020948613/250000000000 : ℝ)^75 := by
    have hnat : (43272801 : ℕ)^91*250000000000^75 ≤ 39020948613^75*200000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43272801 200000000 39020948613 250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8694219913/10000000000 : ℝ)^91 ≤ (42192619712307/50000000000000 : ℝ)^75 := by
    have hnat : (8694219913 : ℕ)^91*50000000000000^75 ≤ 42192619712307^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8694219913 10000000000 42192619712307 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3487363/10000000000 : ℝ), (43272801/200000000 : ℝ), (8694219913/10000000000 : ℝ)] ![(1276222933/20000000000000 : ℝ), (39020948613/250000000000 : ℝ), (42192619712307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3487363/10000000000 : ℝ)|^91 ≤ (1276222933/20000000000000 : ℝ)^75
        have hw : |(-3487363/10000000000 : ℝ)|=(3487363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43272801/200000000 : ℝ)|^91 ≤ (39020948613/250000000000 : ℝ)^75
        have hw : |(43272801/200000000 : ℝ)|=(43272801/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8694219913/10000000000 : ℝ)|^91 ≤ (42192619712307/50000000000000 : ℝ)^75
        have hw : |(8694219913/10000000000 : ℝ)|=(8694219913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4327751193/5000000000 : ℝ)*x 0 + (-46832271/312500000 : ℝ)*x 1 + (124246861/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327751193/5000000000 : ℝ)^91 ≤ (83929499560491/100000000000000 : ℝ)^75 := by
    have hnat : (4327751193 : ℕ)^91*100000000000000^75 ≤ 83929499560491^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327751193 5000000000 83929499560491 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46832271/312500000 : ℝ)^91 ≤ (9996397220859/100000000000000 : ℝ)^75 := by
    have hnat : (46832271 : ℕ)^91*100000000000000^75 ≤ 9996397220859^75*312500000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46832271 312500000 9996397220859 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124246861/1250000000 : ℝ)^91 ≤ (6074103209743/100000000000000 : ℝ)^75 := by
    have hnat : (124246861 : ℕ)^91*100000000000000^75 ≤ 6074103209743^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124246861 1250000000 6074103209743 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327751193/5000000000 : ℝ), (-46832271/312500000 : ℝ), (124246861/1250000000 : ℝ)] ![(83929499560491/100000000000000 : ℝ), (9996397220859/100000000000000 : ℝ), (6074103209743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327751193/5000000000 : ℝ)|^91 ≤ (83929499560491/100000000000000 : ℝ)^75
        have hw : |(4327751193/5000000000 : ℝ)|=(4327751193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-46832271/312500000 : ℝ)|^91 ≤ (9996397220859/100000000000000 : ℝ)^75
        have hw : |(-46832271/312500000 : ℝ)|=(46832271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(124246861/1250000000 : ℝ)|^91 ≤ (6074103209743/100000000000000 : ℝ)^75
        have hw : |(124246861/1250000000 : ℝ)|=(124246861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_16 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3448452561/5000000000 : ℝ)*x 0 + (65910261/156250000 : ℝ)*x 1 + (-10431569/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3448452561/5000000000 : ℝ)^91 ≤ (6371384656017/10000000000000 : ℝ)^75 := by
    have hnat : (3448452561 : ℕ)^91*10000000000000^75 ≤ 6371384656017^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448452561 5000000000 6371384656017 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65910261/156250000 : ℝ)^91 ≤ (1754411171927/5000000000000 : ℝ)^75 := by
    have hnat : (65910261 : ℕ)^91*5000000000000^75 ≤ 1754411171927^75*156250000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65910261 156250000 1754411171927 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10431569/400000000 : ℝ)^91 ≤ (239585996261/20000000000000 : ℝ)^75 := by
    have hnat : (10431569 : ℕ)^91*20000000000000^75 ≤ 239585996261^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10431569 400000000 239585996261 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3448452561/5000000000 : ℝ), (65910261/156250000 : ℝ), (-10431569/400000000 : ℝ)] ![(6371384656017/10000000000000 : ℝ), (1754411171927/5000000000000 : ℝ), (239585996261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3448452561/5000000000 : ℝ)|^91 ≤ (6371384656017/10000000000000 : ℝ)^75
        have hw : |(3448452561/5000000000 : ℝ)|=(3448452561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65910261/156250000 : ℝ)|^91 ≤ (1754411171927/5000000000000 : ℝ)^75
        have hw : |(65910261/156250000 : ℝ)|=(65910261/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10431569/400000000 : ℝ)|^91 ≤ (239585996261/20000000000000 : ℝ)^75
        have hw : |(-10431569/400000000 : ℝ)|=(10431569/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (332775727/1250000000 : ℝ)*x 0 + (250695877/1250000000 : ℝ)*x 1 + (7072784033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332775727/1250000000 : ℝ)^91 ≤ (20073657436489/100000000000000 : ℝ)^75 := by
    have hnat : (332775727 : ℕ)^91*100000000000000^75 ≤ 20073657436489^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332775727 1250000000 20073657436489 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250695877/1250000000 : ℝ)^91 ≤ (14235774825201/100000000000000 : ℝ)^75 := by
    have hnat : (250695877 : ℕ)^91*100000000000000^75 ≤ 14235774825201^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250695877 1250000000 14235774825201 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7072784033/10000000000 : ℝ)^91 ≤ (65690567717389/100000000000000 : ℝ)^75 := by
    have hnat : (7072784033 : ℕ)^91*100000000000000^75 ≤ 65690567717389^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7072784033 10000000000 65690567717389 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332775727/1250000000 : ℝ), (250695877/1250000000 : ℝ), (7072784033/10000000000 : ℝ)] ![(20073657436489/100000000000000 : ℝ), (14235774825201/100000000000000 : ℝ), (65690567717389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332775727/1250000000 : ℝ)|^91 ≤ (20073657436489/100000000000000 : ℝ)^75
        have hw : |(332775727/1250000000 : ℝ)|=(332775727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250695877/1250000000 : ℝ)|^91 ≤ (14235774825201/100000000000000 : ℝ)^75
        have hw : |(250695877/1250000000 : ℝ)|=(250695877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7072784033/10000000000 : ℝ)|^91 ≤ (65690567717389/100000000000000 : ℝ)^75
        have hw : |(7072784033/10000000000 : ℝ)|=(7072784033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-10431569/400000000 : ℝ)*x 0 + (3448452561/5000000000 : ℝ)*x 1 + (65910261/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10431569/400000000 : ℝ)^91 ≤ (239585996261/20000000000000 : ℝ)^75 := by
    have hnat : (10431569 : ℕ)^91*20000000000000^75 ≤ 239585996261^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10431569 400000000 239585996261 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3448452561/5000000000 : ℝ)^91 ≤ (6371384656017/10000000000000 : ℝ)^75 := by
    have hnat : (3448452561 : ℕ)^91*10000000000000^75 ≤ 6371384656017^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448452561 5000000000 6371384656017 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65910261/156250000 : ℝ)^91 ≤ (1754411171927/5000000000000 : ℝ)^75 := by
    have hnat : (65910261 : ℕ)^91*5000000000000^75 ≤ 1754411171927^75*156250000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65910261 156250000 1754411171927 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10431569/400000000 : ℝ), (3448452561/5000000000 : ℝ), (65910261/156250000 : ℝ)] ![(239585996261/20000000000000 : ℝ), (6371384656017/10000000000000 : ℝ), (1754411171927/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10431569/400000000 : ℝ)|^91 ≤ (239585996261/20000000000000 : ℝ)^75
        have hw : |(-10431569/400000000 : ℝ)|=(10431569/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3448452561/5000000000 : ℝ)|^91 ≤ (6371384656017/10000000000000 : ℝ)^75
        have hw : |(3448452561/5000000000 : ℝ)|=(3448452561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65910261/156250000 : ℝ)|^91 ≤ (1754411171927/5000000000000 : ℝ)^75
        have hw : |(65910261/156250000 : ℝ)|=(65910261/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_22 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8694219913/10000000000 : ℝ)*x 0 + (-3487363/10000000000 : ℝ)*x 1 + (43272801/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8694219913/10000000000 : ℝ)^91 ≤ (42192619712307/50000000000000 : ℝ)^75 := by
    have hnat : (8694219913 : ℕ)^91*50000000000000^75 ≤ 42192619712307^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8694219913 10000000000 42192619712307 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3487363/10000000000 : ℝ)^91 ≤ (1276222933/20000000000000 : ℝ)^75 := by
    have hnat : (3487363 : ℕ)^91*20000000000000^75 ≤ 1276222933^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3487363 10000000000 1276222933 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43272801/200000000 : ℝ)^91 ≤ (39020948613/250000000000 : ℝ)^75 := by
    have hnat : (43272801 : ℕ)^91*250000000000^75 ≤ 39020948613^75*200000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43272801 200000000 39020948613 250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8694219913/10000000000 : ℝ), (-3487363/10000000000 : ℝ), (43272801/200000000 : ℝ)] ![(42192619712307/50000000000000 : ℝ), (1276222933/20000000000000 : ℝ), (39020948613/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8694219913/10000000000 : ℝ)|^91 ≤ (42192619712307/50000000000000 : ℝ)^75
        have hw : |(8694219913/10000000000 : ℝ)|=(8694219913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3487363/10000000000 : ℝ)|^91 ≤ (1276222933/20000000000000 : ℝ)^75
        have hw : |(-3487363/10000000000 : ℝ)|=(3487363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43272801/200000000 : ℝ)|^91 ≤ (39020948613/250000000000 : ℝ)^75
        have hw : |(43272801/200000000 : ℝ)|=(43272801/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_23 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (124246861/1250000000 : ℝ)*x 0 + (4327751193/5000000000 : ℝ)*x 1 + (-46832271/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (124246861/1250000000 : ℝ)^91 ≤ (6074103209743/100000000000000 : ℝ)^75 := by
    have hnat : (124246861 : ℕ)^91*100000000000000^75 ≤ 6074103209743^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124246861 1250000000 6074103209743 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4327751193/5000000000 : ℝ)^91 ≤ (83929499560491/100000000000000 : ℝ)^75 := by
    have hnat : (4327751193 : ℕ)^91*100000000000000^75 ≤ 83929499560491^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327751193 5000000000 83929499560491 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46832271/312500000 : ℝ)^91 ≤ (9996397220859/100000000000000 : ℝ)^75 := by
    have hnat : (46832271 : ℕ)^91*100000000000000^75 ≤ 9996397220859^75*312500000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46832271 312500000 9996397220859 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(124246861/1250000000 : ℝ), (4327751193/5000000000 : ℝ), (-46832271/312500000 : ℝ)] ![(6074103209743/100000000000000 : ℝ), (83929499560491/100000000000000 : ℝ), (9996397220859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(124246861/1250000000 : ℝ)|^91 ≤ (6074103209743/100000000000000 : ℝ)^75
        have hw : |(124246861/1250000000 : ℝ)|=(124246861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4327751193/5000000000 : ℝ)|^91 ≤ (83929499560491/100000000000000 : ℝ)^75
        have hw : |(4327751193/5000000000 : ℝ)|=(4327751193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46832271/312500000 : ℝ)|^91 ≤ (9996397220859/100000000000000 : ℝ)^75
        have hw : |(-46832271/312500000 : ℝ)|=(46832271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s0_27 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7072784033/10000000000 : ℝ)*x 0 + (332775727/1250000000 : ℝ)*x 1 + (250695877/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7072784033/10000000000 : ℝ)^91 ≤ (65690567717389/100000000000000 : ℝ)^75 := by
    have hnat : (7072784033 : ℕ)^91*100000000000000^75 ≤ 65690567717389^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7072784033 10000000000 65690567717389 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (332775727/1250000000 : ℝ)^91 ≤ (20073657436489/100000000000000 : ℝ)^75 := by
    have hnat : (332775727 : ℕ)^91*100000000000000^75 ≤ 20073657436489^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332775727 1250000000 20073657436489 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250695877/1250000000 : ℝ)^91 ≤ (14235774825201/100000000000000 : ℝ)^75 := by
    have hnat : (250695877 : ℕ)^91*100000000000000^75 ≤ 14235774825201^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250695877 1250000000 14235774825201 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7072784033/10000000000 : ℝ), (332775727/1250000000 : ℝ), (250695877/1250000000 : ℝ)] ![(65690567717389/100000000000000 : ℝ), (20073657436489/100000000000000 : ℝ), (14235774825201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7072784033/10000000000 : ℝ)|^91 ≤ (65690567717389/100000000000000 : ℝ)^75
        have hw : |(7072784033/10000000000 : ℝ)|=(7072784033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(332775727/1250000000 : ℝ)|^91 ≤ (20073657436489/100000000000000 : ℝ)^75
        have hw : |(332775727/1250000000 : ℝ)|=(332775727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(250695877/1250000000 : ℝ)|^91 ≤ (14235774825201/100000000000000 : ℝ)^75
        have hw : |(250695877/1250000000 : ℝ)|=(250695877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-501815753/5000000000 : ℝ)*x 0 + (2678721843/5000000000 : ℝ)*x 1 + (1340828253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501815753/5000000000 : ℝ)^91 ≤ (6145777040011/100000000000000 : ℝ)^75 := by
    have hnat : (501815753 : ℕ)^91*100000000000000^75 ≤ 6145777040011^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501815753 5000000000 6145777040011 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2678721843/5000000000 : ℝ)^91 ≤ (46895939324039/100000000000000 : ℝ)^75 := by
    have hnat : (2678721843 : ℕ)^91*100000000000000^75 ≤ 46895939324039^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678721843 5000000000 46895939324039 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1340828253/2500000000 : ℝ)^91 ≤ (5869785452393/12500000000000 : ℝ)^75 := by
    have hnat : (1340828253 : ℕ)^91*12500000000000^75 ≤ 5869785452393^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340828253 2500000000 5869785452393 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-501815753/5000000000 : ℝ), (2678721843/5000000000 : ℝ), (1340828253/2500000000 : ℝ)] ![(6145777040011/100000000000000 : ℝ), (46895939324039/100000000000000 : ℝ), (5869785452393/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-501815753/5000000000 : ℝ)|^91 ≤ (6145777040011/100000000000000 : ℝ)^75
        have hw : |(-501815753/5000000000 : ℝ)|=(501815753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2678721843/5000000000 : ℝ)|^91 ≤ (46895939324039/100000000000000 : ℝ)^75
        have hw : |(2678721843/5000000000 : ℝ)|=(2678721843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1340828253/2500000000 : ℝ)|^91 ≤ (5869785452393/12500000000000 : ℝ)^75
        have hw : |(1340828253/2500000000 : ℝ)|=(1340828253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (134082813/250000000 : ℝ)*x 0 + (-1003631417/10000000000 : ℝ)*x 1 + (66968053/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134082813/250000000 : ℝ)^91 ≤ (11739569598121/25000000000000 : ℝ)^75 := by
    have hnat : (134082813 : ℕ)^91*25000000000000^75 ≤ 11739569598121^75*250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134082813 250000000 11739569598121 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003631417/10000000000 : ℝ)^91 ≤ (6145776378751/100000000000000 : ℝ)^75 := by
    have hnat : (1003631417 : ℕ)^91*100000000000000^75 ≤ 6145776378751^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003631417 10000000000 6145776378751 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66968053/125000000 : ℝ)^91 ≤ (46895945207969/100000000000000 : ℝ)^75 := by
    have hnat : (66968053 : ℕ)^91*100000000000000^75 ≤ 46895945207969^75*125000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66968053 125000000 46895945207969 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134082813/250000000 : ℝ), (-1003631417/10000000000 : ℝ), (66968053/125000000 : ℝ)] ![(11739569598121/25000000000000 : ℝ), (6145776378751/100000000000000 : ℝ), (46895945207969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134082813/250000000 : ℝ)|^91 ≤ (11739569598121/25000000000000 : ℝ)^75
        have hw : |(134082813/250000000 : ℝ)|=(134082813/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1003631417/10000000000 : ℝ)|^91 ≤ (6145776378751/100000000000000 : ℝ)^75
        have hw : |(-1003631417/10000000000 : ℝ)|=(1003631417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66968053/125000000 : ℝ)|^91 ≤ (46895945207969/100000000000000 : ℝ)^75
        have hw : |(66968053/125000000 : ℝ)|=(66968053/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5357443823/10000000000 : ℝ)*x 0 + (1340828257/2500000000 : ℝ)*x 1 + (-125453911/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357443823/10000000000 : ℝ)^91 ≤ (4689594077909/10000000000000 : ℝ)^75 := by
    have hnat : (5357443823 : ℕ)^91*10000000000000^75 ≤ 4689594077909^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357443823 10000000000 4689594077909 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1340828257/2500000000 : ℝ)^91 ≤ (46958283789117/100000000000000 : ℝ)^75 := by
    have hnat : (1340828257 : ℕ)^91*100000000000000^75 ≤ 46958283789117^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340828257 2500000000 46958283789117 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125453911/1250000000 : ℝ)^91 ≤ (3072887710147/50000000000000 : ℝ)^75 := by
    have hnat : (125453911 : ℕ)^91*50000000000000^75 ≤ 3072887710147^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125453911 1250000000 3072887710147 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357443823/10000000000 : ℝ), (1340828257/2500000000 : ℝ), (-125453911/1250000000 : ℝ)] ![(4689594077909/10000000000000 : ℝ), (46958283789117/100000000000000 : ℝ), (3072887710147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357443823/10000000000 : ℝ)|^91 ≤ (4689594077909/10000000000000 : ℝ)^75
        have hw : |(5357443823/10000000000 : ℝ)|=(5357443823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1340828257/2500000000 : ℝ)|^91 ≤ (46958283789117/100000000000000 : ℝ)^75
        have hw : |(1340828257/2500000000 : ℝ)|=(1340828257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-125453911/1250000000 : ℝ)|^91 ≤ (3072887710147/50000000000000 : ℝ)^75
        have hw : |(-125453911/1250000000 : ℝ)|=(125453911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-919849417/10000000000 : ℝ)*x 0 + (1119149161/2500000000 : ℝ)*x 1 + (6270172571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (919849417/10000000000 : ℝ)^91 ≤ (1382238493823/25000000000000 : ℝ)^75 := by
    have hnat : (919849417 : ℕ)^91*25000000000000^75 ≤ 1382238493823^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919849417 10000000000 1382238493823 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119149161/2500000000 : ℝ)^91 ≤ (37712344340489/100000000000000 : ℝ)^75 := by
    have hnat : (1119149161 : ℕ)^91*100000000000000^75 ≤ 37712344340489^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119149161 2500000000 37712344340489 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6270172571/10000000000 : ℝ)^91 ≤ (56758701665383/100000000000000 : ℝ)^75 := by
    have hnat : (6270172571 : ℕ)^91*100000000000000^75 ≤ 56758701665383^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6270172571 10000000000 56758701665383 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-919849417/10000000000 : ℝ), (1119149161/2500000000 : ℝ), (6270172571/10000000000 : ℝ)] ![(1382238493823/25000000000000 : ℝ), (37712344340489/100000000000000 : ℝ), (56758701665383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-919849417/10000000000 : ℝ)|^91 ≤ (1382238493823/25000000000000 : ℝ)^75
        have hw : |(-919849417/10000000000 : ℝ)|=(919849417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119149161/2500000000 : ℝ)|^91 ≤ (37712344340489/100000000000000 : ℝ)^75
        have hw : |(1119149161/2500000000 : ℝ)|=(1119149161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6270172571/10000000000 : ℝ)|^91 ≤ (56758701665383/100000000000000 : ℝ)^75
        have hw : |(6270172571/10000000000 : ℝ)|=(6270172571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2820376511/5000000000 : ℝ)*x 0 + (-40652091/2000000000 : ℝ)*x 1 + (5572810319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2820376511/5000000000 : ℝ)^91 ≤ (49921657475017/100000000000000 : ℝ)^75 := by
    have hnat : (2820376511 : ℕ)^91*100000000000000^75 ≤ 49921657475017^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820376511 5000000000 49921657475017 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40652091/2000000000 : ℝ)^91 ≤ (885327954351/100000000000000 : ℝ)^75 := by
    have hnat : (40652091 : ℕ)^91*100000000000000^75 ≤ 885327954351^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40652091 2000000000 885327954351 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5572810319/10000000000 : ℝ)^91 ≤ (49193014557511/100000000000000 : ℝ)^75 := by
    have hnat : (5572810319 : ℕ)^91*100000000000000^75 ≤ 49193014557511^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5572810319 10000000000 49193014557511 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2820376511/5000000000 : ℝ), (-40652091/2000000000 : ℝ), (5572810319/10000000000 : ℝ)] ![(49921657475017/100000000000000 : ℝ), (885327954351/100000000000000 : ℝ), (49193014557511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2820376511/5000000000 : ℝ)|^91 ≤ (49921657475017/100000000000000 : ℝ)^75
        have hw : |(2820376511/5000000000 : ℝ)|=(2820376511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40652091/2000000000 : ℝ)|^91 ≤ (885327954351/100000000000000 : ℝ)^75
        have hw : |(-40652091/2000000000 : ℝ)|=(40652091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5572810319/10000000000 : ℝ)|^91 ≤ (49193014557511/100000000000000 : ℝ)^75
        have hw : |(5572810319/10000000000 : ℝ)|=(5572810319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (538743171/1250000000 : ℝ)*x 0 + (1372288701/2000000000 : ℝ)*x 1 + (-5033937/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538743171/1250000000 : ℝ)^91 ≤ (36015745467891/100000000000000 : ℝ)^75 := by
    have hnat : (538743171 : ℕ)^91*100000000000000^75 ≤ 36015745467891^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538743171 1250000000 36015745467891 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372288701/2000000000 : ℝ)^91 ≤ (12663316429267/20000000000000 : ℝ)^75 := by
    have hnat : (1372288701 : ℕ)^91*20000000000000^75 ≤ 12663316429267^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372288701 2000000000 12663316429267 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5033937/312500000 : ℝ)^91 ≤ (41729523531/6250000000000 : ℝ)^75 := by
    have hnat : (5033937 : ℕ)^91*6250000000000^75 ≤ 41729523531^75*312500000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033937 312500000 41729523531 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538743171/1250000000 : ℝ), (1372288701/2000000000 : ℝ), (-5033937/312500000 : ℝ)] ![(36015745467891/100000000000000 : ℝ), (12663316429267/20000000000000 : ℝ), (41729523531/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538743171/1250000000 : ℝ)|^91 ≤ (36015745467891/100000000000000 : ℝ)^75
        have hw : |(538743171/1250000000 : ℝ)|=(538743171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372288701/2000000000 : ℝ)|^91 ≤ (12663316429267/20000000000000 : ℝ)^75
        have hw : |(1372288701/2000000000 : ℝ)|=(1372288701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5033937/312500000 : ℝ)|^91 ≤ (41729523531/6250000000000 : ℝ)^75
        have hw : |(-5033937/312500000 : ℝ)|=(5033937/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (710519111/2000000000 : ℝ)*x 0 + (501817821/1000000000 : ℝ)*x 1 + (176120381/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (710519111/2000000000 : ℝ)^91 ≤ (28488015607579/100000000000000 : ℝ)^75 := by
    have hnat : (710519111 : ℕ)^91*100000000000000^75 ≤ 28488015607579^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710519111 2000000000 28488015607579 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501817821/1000000000 : ℝ)^91 ≤ (10829354886193/25000000000000 : ℝ)^75 := by
    have hnat : (501817821 : ℕ)^91*25000000000000^75 ≤ 10829354886193^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501817821 1000000000 10829354886193 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176120381/500000000 : ℝ)^91 ≤ (14097282415019/50000000000000 : ℝ)^75 := by
    have hnat : (176120381 : ℕ)^91*50000000000000^75 ≤ 14097282415019^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176120381 500000000 14097282415019 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(710519111/2000000000 : ℝ), (501817821/1000000000 : ℝ), (176120381/500000000 : ℝ)] ![(28488015607579/100000000000000 : ℝ), (10829354886193/25000000000000 : ℝ), (14097282415019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(710519111/2000000000 : ℝ)|^91 ≤ (28488015607579/100000000000000 : ℝ)^75
        have hw : |(710519111/2000000000 : ℝ)|=(710519111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501817821/1000000000 : ℝ)|^91 ≤ (10829354886193/25000000000000 : ℝ)^75
        have hw : |(501817821/1000000000 : ℝ)|=(501817821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176120381/500000000 : ℝ)|^91 ≤ (14097282415019/50000000000000 : ℝ)^75
        have hw : |(176120381/500000000 : ℝ)|=(176120381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5033937/312500000 : ℝ)*x 0 + (538743171/1250000000 : ℝ)*x 1 + (1372288701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5033937/312500000 : ℝ)^91 ≤ (41729523531/6250000000000 : ℝ)^75 := by
    have hnat : (5033937 : ℕ)^91*6250000000000^75 ≤ 41729523531^75*312500000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033937 312500000 41729523531 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538743171/1250000000 : ℝ)^91 ≤ (36015745467891/100000000000000 : ℝ)^75 := by
    have hnat : (538743171 : ℕ)^91*100000000000000^75 ≤ 36015745467891^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538743171 1250000000 36015745467891 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372288701/2000000000 : ℝ)^91 ≤ (12663316429267/20000000000000 : ℝ)^75 := by
    have hnat : (1372288701 : ℕ)^91*20000000000000^75 ≤ 12663316429267^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372288701 2000000000 12663316429267 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5033937/312500000 : ℝ), (538743171/1250000000 : ℝ), (1372288701/2000000000 : ℝ)] ![(41729523531/6250000000000 : ℝ), (36015745467891/100000000000000 : ℝ), (12663316429267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5033937/312500000 : ℝ)|^91 ≤ (41729523531/6250000000000 : ℝ)^75
        have hw : |(-5033937/312500000 : ℝ)|=(5033937/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538743171/1250000000 : ℝ)|^91 ≤ (36015745467891/100000000000000 : ℝ)^75
        have hw : |(538743171/1250000000 : ℝ)|=(538743171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372288701/2000000000 : ℝ)|^91 ≤ (12663316429267/20000000000000 : ℝ)^75
        have hw : |(1372288701/2000000000 : ℝ)|=(1372288701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6270172571/10000000000 : ℝ)*x 0 + (-919849417/10000000000 : ℝ)*x 1 + (1119149161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6270172571/10000000000 : ℝ)^91 ≤ (56758701665383/100000000000000 : ℝ)^75 := by
    have hnat : (6270172571 : ℕ)^91*100000000000000^75 ≤ 56758701665383^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6270172571 10000000000 56758701665383 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (919849417/10000000000 : ℝ)^91 ≤ (1382238493823/25000000000000 : ℝ)^75 := by
    have hnat : (919849417 : ℕ)^91*25000000000000^75 ≤ 1382238493823^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919849417 10000000000 1382238493823 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119149161/2500000000 : ℝ)^91 ≤ (37712344340489/100000000000000 : ℝ)^75 := by
    have hnat : (1119149161 : ℕ)^91*100000000000000^75 ≤ 37712344340489^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119149161 2500000000 37712344340489 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6270172571/10000000000 : ℝ), (-919849417/10000000000 : ℝ), (1119149161/2500000000 : ℝ)] ![(56758701665383/100000000000000 : ℝ), (1382238493823/25000000000000 : ℝ), (37712344340489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6270172571/10000000000 : ℝ)|^91 ≤ (56758701665383/100000000000000 : ℝ)^75
        have hw : |(6270172571/10000000000 : ℝ)|=(6270172571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-919849417/10000000000 : ℝ)|^91 ≤ (1382238493823/25000000000000 : ℝ)^75
        have hw : |(-919849417/10000000000 : ℝ)|=(919849417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119149161/2500000000 : ℝ)|^91 ≤ (37712344340489/100000000000000 : ℝ)^75
        have hw : |(1119149161/2500000000 : ℝ)|=(1119149161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_16 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5572810319/10000000000 : ℝ)*x 0 + (2820376511/5000000000 : ℝ)*x 1 + (-40652091/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5572810319/10000000000 : ℝ)^91 ≤ (49193014557511/100000000000000 : ℝ)^75 := by
    have hnat : (5572810319 : ℕ)^91*100000000000000^75 ≤ 49193014557511^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5572810319 10000000000 49193014557511 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2820376511/5000000000 : ℝ)^91 ≤ (49921657475017/100000000000000 : ℝ)^75 := by
    have hnat : (2820376511 : ℕ)^91*100000000000000^75 ≤ 49921657475017^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820376511 5000000000 49921657475017 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40652091/2000000000 : ℝ)^91 ≤ (885327954351/100000000000000 : ℝ)^75 := by
    have hnat : (40652091 : ℕ)^91*100000000000000^75 ≤ 885327954351^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40652091 2000000000 885327954351 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5572810319/10000000000 : ℝ), (2820376511/5000000000 : ℝ), (-40652091/2000000000 : ℝ)] ![(49193014557511/100000000000000 : ℝ), (49921657475017/100000000000000 : ℝ), (885327954351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5572810319/10000000000 : ℝ)|^91 ≤ (49193014557511/100000000000000 : ℝ)^75
        have hw : |(5572810319/10000000000 : ℝ)|=(5572810319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2820376511/5000000000 : ℝ)|^91 ≤ (49921657475017/100000000000000 : ℝ)^75
        have hw : |(2820376511/5000000000 : ℝ)|=(2820376511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40652091/2000000000 : ℝ)|^91 ≤ (885327954351/100000000000000 : ℝ)^75
        have hw : |(-40652091/2000000000 : ℝ)|=(40652091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (176120381/500000000 : ℝ)*x 0 + (710519111/2000000000 : ℝ)*x 1 + (501817821/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176120381/500000000 : ℝ)^91 ≤ (14097282415019/50000000000000 : ℝ)^75 := by
    have hnat : (176120381 : ℕ)^91*50000000000000^75 ≤ 14097282415019^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176120381 500000000 14097282415019 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (710519111/2000000000 : ℝ)^91 ≤ (28488015607579/100000000000000 : ℝ)^75 := by
    have hnat : (710519111 : ℕ)^91*100000000000000^75 ≤ 28488015607579^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710519111 2000000000 28488015607579 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501817821/1000000000 : ℝ)^91 ≤ (10829354886193/25000000000000 : ℝ)^75 := by
    have hnat : (501817821 : ℕ)^91*25000000000000^75 ≤ 10829354886193^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501817821 1000000000 10829354886193 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(176120381/500000000 : ℝ), (710519111/2000000000 : ℝ), (501817821/1000000000 : ℝ)] ![(14097282415019/50000000000000 : ℝ), (28488015607579/100000000000000 : ℝ), (10829354886193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(176120381/500000000 : ℝ)|^91 ≤ (14097282415019/50000000000000 : ℝ)^75
        have hw : |(176120381/500000000 : ℝ)|=(176120381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(710519111/2000000000 : ℝ)|^91 ≤ (28488015607579/100000000000000 : ℝ)^75
        have hw : |(710519111/2000000000 : ℝ)|=(710519111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501817821/1000000000 : ℝ)|^91 ≤ (10829354886193/25000000000000 : ℝ)^75
        have hw : |(501817821/1000000000 : ℝ)|=(501817821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-40652091/2000000000 : ℝ)*x 0 + (5572810319/10000000000 : ℝ)*x 1 + (2820376511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40652091/2000000000 : ℝ)^91 ≤ (885327954351/100000000000000 : ℝ)^75 := by
    have hnat : (40652091 : ℕ)^91*100000000000000^75 ≤ 885327954351^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40652091 2000000000 885327954351 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5572810319/10000000000 : ℝ)^91 ≤ (49193014557511/100000000000000 : ℝ)^75 := by
    have hnat : (5572810319 : ℕ)^91*100000000000000^75 ≤ 49193014557511^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5572810319 10000000000 49193014557511 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2820376511/5000000000 : ℝ)^91 ≤ (49921657475017/100000000000000 : ℝ)^75 := by
    have hnat : (2820376511 : ℕ)^91*100000000000000^75 ≤ 49921657475017^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820376511 5000000000 49921657475017 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40652091/2000000000 : ℝ), (5572810319/10000000000 : ℝ), (2820376511/5000000000 : ℝ)] ![(885327954351/100000000000000 : ℝ), (49193014557511/100000000000000 : ℝ), (49921657475017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40652091/2000000000 : ℝ)|^91 ≤ (885327954351/100000000000000 : ℝ)^75
        have hw : |(-40652091/2000000000 : ℝ)|=(40652091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5572810319/10000000000 : ℝ)|^91 ≤ (49193014557511/100000000000000 : ℝ)^75
        have hw : |(5572810319/10000000000 : ℝ)|=(5572810319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2820376511/5000000000 : ℝ)|^91 ≤ (49921657475017/100000000000000 : ℝ)^75
        have hw : |(2820376511/5000000000 : ℝ)|=(2820376511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_22 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1372288701/2000000000 : ℝ)*x 0 + (-5033937/312500000 : ℝ)*x 1 + (538743171/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1372288701/2000000000 : ℝ)^91 ≤ (12663316429267/20000000000000 : ℝ)^75 := by
    have hnat : (1372288701 : ℕ)^91*20000000000000^75 ≤ 12663316429267^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372288701 2000000000 12663316429267 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5033937/312500000 : ℝ)^91 ≤ (41729523531/6250000000000 : ℝ)^75 := by
    have hnat : (5033937 : ℕ)^91*6250000000000^75 ≤ 41729523531^75*312500000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033937 312500000 41729523531 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538743171/1250000000 : ℝ)^91 ≤ (36015745467891/100000000000000 : ℝ)^75 := by
    have hnat : (538743171 : ℕ)^91*100000000000000^75 ≤ 36015745467891^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538743171 1250000000 36015745467891 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1372288701/2000000000 : ℝ), (-5033937/312500000 : ℝ), (538743171/1250000000 : ℝ)] ![(12663316429267/20000000000000 : ℝ), (41729523531/6250000000000 : ℝ), (36015745467891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1372288701/2000000000 : ℝ)|^91 ≤ (12663316429267/20000000000000 : ℝ)^75
        have hw : |(1372288701/2000000000 : ℝ)|=(1372288701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5033937/312500000 : ℝ)|^91 ≤ (41729523531/6250000000000 : ℝ)^75
        have hw : |(-5033937/312500000 : ℝ)|=(5033937/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538743171/1250000000 : ℝ)|^91 ≤ (36015745467891/100000000000000 : ℝ)^75
        have hw : |(538743171/1250000000 : ℝ)|=(538743171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_23 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1119149161/2500000000 : ℝ)*x 0 + (6270172571/10000000000 : ℝ)*x 1 + (-919849417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119149161/2500000000 : ℝ)^91 ≤ (37712344340489/100000000000000 : ℝ)^75 := by
    have hnat : (1119149161 : ℕ)^91*100000000000000^75 ≤ 37712344340489^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119149161 2500000000 37712344340489 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6270172571/10000000000 : ℝ)^91 ≤ (56758701665383/100000000000000 : ℝ)^75 := by
    have hnat : (6270172571 : ℕ)^91*100000000000000^75 ≤ 56758701665383^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6270172571 10000000000 56758701665383 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919849417/10000000000 : ℝ)^91 ≤ (1382238493823/25000000000000 : ℝ)^75 := by
    have hnat : (919849417 : ℕ)^91*25000000000000^75 ≤ 1382238493823^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919849417 10000000000 1382238493823 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119149161/2500000000 : ℝ), (6270172571/10000000000 : ℝ), (-919849417/10000000000 : ℝ)] ![(37712344340489/100000000000000 : ℝ), (56758701665383/100000000000000 : ℝ), (1382238493823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119149161/2500000000 : ℝ)|^91 ≤ (37712344340489/100000000000000 : ℝ)^75
        have hw : |(1119149161/2500000000 : ℝ)|=(1119149161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6270172571/10000000000 : ℝ)|^91 ≤ (56758701665383/100000000000000 : ℝ)^75
        have hw : |(6270172571/10000000000 : ℝ)|=(6270172571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-919849417/10000000000 : ℝ)|^91 ≤ (1382238493823/25000000000000 : ℝ)^75
        have hw : |(-919849417/10000000000 : ℝ)|=(919849417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327087_s1_27 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (501817821/1000000000 : ℝ)*x 0 + (176120381/500000000 : ℝ)*x 1 + (710519111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501817821/1000000000 : ℝ)^91 ≤ (10829354886193/25000000000000 : ℝ)^75 := by
    have hnat : (501817821 : ℕ)^91*25000000000000^75 ≤ 10829354886193^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501817821 1000000000 10829354886193 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176120381/500000000 : ℝ)^91 ≤ (14097282415019/50000000000000 : ℝ)^75 := by
    have hnat : (176120381 : ℕ)^91*50000000000000^75 ≤ 14097282415019^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176120381 500000000 14097282415019 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (710519111/2000000000 : ℝ)^91 ≤ (28488015607579/100000000000000 : ℝ)^75 := by
    have hnat : (710519111 : ℕ)^91*100000000000000^75 ≤ 28488015607579^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710519111 2000000000 28488015607579 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(501817821/1000000000 : ℝ), (176120381/500000000 : ℝ), (710519111/2000000000 : ℝ)] ![(10829354886193/25000000000000 : ℝ), (14097282415019/50000000000000 : ℝ), (28488015607579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(501817821/1000000000 : ℝ)|^91 ≤ (10829354886193/25000000000000 : ℝ)^75
        have hw : |(501817821/1000000000 : ℝ)|=(501817821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(176120381/500000000 : ℝ)|^91 ≤ (14097282415019/50000000000000 : ℝ)^75
        have hw : |(176120381/500000000 : ℝ)|=(176120381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(710519111/2000000000 : ℝ)|^91 ≤ (28488015607579/100000000000000 : ℝ)^75
        have hw : |(710519111/2000000000 : ℝ)|=(710519111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327087 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((32203/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32203/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((32203/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(32203/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32203/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32203/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (32523/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-92991719/5000000000 : ℝ)*X 0 0+(5457472651/10000000000 : ℝ)*X 0 1+(1440919367/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1440919367/2500000000 : ℝ)*X 1 0+(-92991719/5000000000 : ℝ)*X 1 1+(5457472651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5457472651/10000000000 : ℝ)*X 2 0+(1440919367/2500000000 : ℝ)*X 2 1+(-92991719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-46832271/312500000 : ℝ)*X 0 0+(124246861/1250000000 : ℝ)*X 0 1+(4327751193/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((65910261/156250000 : ℝ)*X 1 0+(-10431569/400000000 : ℝ)*X 1 1+(3448452561/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((43272801/200000000 : ℝ)*X 2 0+(8694219913/10000000000 : ℝ)*X 2 1+(-3487363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((250695877/1250000000 : ℝ)*X 0 0+(7072784033/10000000000 : ℝ)*X 0 1+(332775727/1250000000 : ℝ)*X 0 2+(250695877/1250000000 : ℝ)*X 1 0+(7072784033/10000000000 : ℝ)*X 1 1+(332775727/1250000000 : ℝ)*X 1 2+(250695877/1250000000 : ℝ)*X 2 0+(7072784033/10000000000 : ℝ)*X 2 1+(332775727/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-3487363/10000000000 : ℝ)*X 0 0+(43272801/200000000 : ℝ)*X 0 1+(8694219913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4327751193/5000000000 : ℝ)*X 1 0+(-46832271/312500000 : ℝ)*X 1 1+(124246861/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3448452561/5000000000 : ℝ)*X 2 0+(65910261/156250000 : ℝ)*X 2 1+(-10431569/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((332775727/1250000000 : ℝ)*X 0 0+(250695877/1250000000 : ℝ)*X 0 1+(7072784033/10000000000 : ℝ)*X 0 2+(332775727/1250000000 : ℝ)*X 1 0+(250695877/1250000000 : ℝ)*X 1 1+(7072784033/10000000000 : ℝ)*X 1 2+(332775727/1250000000 : ℝ)*X 2 0+(250695877/1250000000 : ℝ)*X 2 1+(7072784033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-10431569/400000000 : ℝ)*X 0 0+(3448452561/5000000000 : ℝ)*X 0 1+(65910261/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8694219913/10000000000 : ℝ)*X 1 0+(-3487363/10000000000 : ℝ)*X 1 1+(43272801/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((124246861/1250000000 : ℝ)*X 2 0+(4327751193/5000000000 : ℝ)*X 2 1+(-46832271/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((7072784033/10000000000 : ℝ)*X 0 0+(332775727/1250000000 : ℝ)*X 0 1+(250695877/1250000000 : ℝ)*X 0 2+(7072784033/10000000000 : ℝ)*X 1 0+(332775727/1250000000 : ℝ)*X 1 1+(250695877/1250000000 : ℝ)*X 1 2+(7072784033/10000000000 : ℝ)*X 2 0+(332775727/1250000000 : ℝ)*X 2 1+(250695877/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((61149/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(61149/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26392670081917685315961/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1183740486833/1000000000000 : ℝ)*(base7) + (2911747/1000000000000 : ℝ)*(base19) + (47170016657/250000000000 : ℝ)*(base50) + (187051/100000000000 : ℝ)*(base53) + (21270608871/500000000000 : ℝ)*(base60) + (1360930541299/1000000000000 : ℝ)*(major_s0_0) + (1360930541299/1000000000000 : ℝ)*(major_s0_1) + (1360928670789/1000000000000 : ℝ)*(major_s0_2) + (2464419/500000000000 : ℝ)*(sp_s0_0) + (1437049433281/1000000000000 : ℝ)*(sp_s0_7) + (71853890093/50000000000 : ℝ)*(sp_s0_8) + (1437082584117/1000000000000 : ℝ)*(sp_s0_9) + (1826868935401/1000000000000 : ℝ)*(sp_s0_13) + (205871/7812500000 : ℝ)*(sp_s0_14) + (80391056071/125000000000 : ℝ)*(f.failure) + (1437082584117/1000000000000 : ℝ)*(f.sum) + (1531357465032139/5000000000000000000000000000 : ℝ)*base62 + (360881737698783/5000000000000000000000000000 : ℝ)*base64 + (3659418222937/2500000000000000000000000000 : ℝ)*base67 + (1133237408058193/2500000000000000000000000000 : ℝ)*base68 + (1277993786747091/5000000000000000000000000000 : ℝ)*base71 + (1247820946915753/5000000000000000000000000000 : ℝ)*base72 + (2902721011915753/5000000000000000000000000000 : ℝ)*base74 + (315233242777063/2500000000000000000000000000 : ℝ)*base76 + (1096369790030121/5000000000000000000000000000 : ℝ)*base79 + (2881/12500000000000000 : ℝ)*base87 + (2881/12500000000000000 : ℝ)*base89 + (2881/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((61149/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(61149/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26392670081917685315961/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1183740486833/1000000000000 : ℝ)*(base7) + (2911747/1000000000000 : ℝ)*(base21) + (187051/100000000000 : ℝ)*(base33) + (21270608871/500000000000 : ℝ)*(base40) + (47170016657/250000000000 : ℝ)*(base60) + (1360928670789/1000000000000 : ℝ)*(major_s0_0) + (1360930541299/1000000000000 : ℝ)*(major_s0_1) + (1360930541299/1000000000000 : ℝ)*(major_s0_2) + (2464419/500000000000 : ℝ)*(sp_s0_1) + (1437082584117/1000000000000 : ℝ)*(sp_s0_14) + (1437049433281/1000000000000 : ℝ)*(sp_s0_15) + (71853890093/50000000000 : ℝ)*(sp_s0_16) + (1826868935401/1000000000000 : ℝ)*(sp_s0_20) + (205871/7812500000 : ℝ)*(sp_s0_22) + (80391056071/125000000000 : ℝ)*(f.failure) + (1437082584117/1000000000000 : ℝ)*(f.sum) + (1096369790030121/5000000000000000000000000000 : ℝ)*base63 + (2902721011915753/5000000000000000000000000000 : ℝ)*base64 + (315233242777063/2500000000000000000000000000 : ℝ)*base66 + (3659418222937/2500000000000000000000000000 : ℝ)*base69 + (1531357465032139/5000000000000000000000000000 : ℝ)*base70 + (360881737698783/5000000000000000000000000000 : ℝ)*base72 + (1247820946915753/5000000000000000000000000000 : ℝ)*base74 + (1133237408058193/2500000000000000000000000000 : ℝ)*base76 + (1277993786747091/5000000000000000000000000000 : ℝ)*base79 + (2881/12500000000000000 : ℝ)*base87 + (2881/12500000000000000 : ℝ)*base89 + (2881/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61149/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61149/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26392670081917685315961/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1183740486833/1000000000000 : ℝ)*(base7) + (2911747/1000000000000 : ℝ)*(base11) + (47170016657/250000000000 : ℝ)*(base40) + (187051/100000000000 : ℝ)*(base43) + (21270608871/500000000000 : ℝ)*(base50) + (1360930541299/1000000000000 : ℝ)*(major_s0_0) + (1360928670789/1000000000000 : ℝ)*(major_s0_1) + (1360930541299/1000000000000 : ℝ)*(major_s0_2) + (2464419/500000000000 : ℝ)*(sp_s0_2) + (205871/7812500000 : ℝ)*(sp_s0_9) + (71853890093/50000000000 : ℝ)*(sp_s0_21) + (1437082584117/1000000000000 : ℝ)*(sp_s0_22) + (1437049433281/1000000000000 : ℝ)*(sp_s0_23) + (1826868935401/1000000000000 : ℝ)*(sp_s0_27) + (80391056071/125000000000 : ℝ)*(f.failure) + (1437082584117/1000000000000 : ℝ)*(f.sum) + (1277993786747091/5000000000000000000000000000 : ℝ)*base63 + (1247820946915753/5000000000000000000000000000 : ℝ)*base64 + (1133237408058193/2500000000000000000000000000 : ℝ)*base66 + (315233242777063/2500000000000000000000000000 : ℝ)*base68 + (1096369790030121/5000000000000000000000000000 : ℝ)*base71 + (2902721011915753/5000000000000000000000000000 : ℝ)*base72 + (360881737698783/5000000000000000000000000000 : ℝ)*base74 + (3659418222937/2500000000000000000000000000 : ℝ)*base77 + (1531357465032139/5000000000000000000000000000 : ℝ)*base78 + (2881/12500000000000000 : ℝ)*base87 + (2881/12500000000000000 : ℝ)*base89 + (2881/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (61149/100000 : ℝ) ^ (89/16 : ℝ) ≤ (202600648995420593/3125000000000000000 : ℝ) := by
    have hpowers : (61149/100000 : ℝ)^89 ≤ (202600648995420593/3125000000000000000 : ℝ)^16 := by
      have hnat : (61149 : ℕ)^89*3125000000000000000^16 ≤ 202600648995420593^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61149 100000 202600648995420593 3125000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61149/100000 : ℝ)) (X := (202600648995420593/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (3327600648995420593/3125000000000000000 : ℝ) ≤ (5056784962993921/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3327600648995420593/3125000000000000000 : ℝ)^16 ≤ (5056784962993921/5000000000000000 : ℝ)^89 := by
      have hnat : (3327600648995420593 : ℕ)^16*5000000000000000^89 ≤ 5056784962993921^89*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3327600648995420593 3125000000000000000 5056784962993921 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056784962993921/5000000000000000 : ℝ)) (X := (3327600648995420593/3125000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1765100648995420593/1562500000000000000 : ℝ) ≤ (638850176833261/625000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (1765100648995420593/1562500000000000000 : ℝ)^16 ≤ (638850176833261/625000000000000 : ℝ)^89 := by
      have hnat : (1765100648995420593 : ℕ)^16*625000000000000^89 ≤ 638850176833261^89*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1765100648995420593 1562500000000000000 638850176833261 625000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (638850176833261/625000000000000 : ℝ)) (X := (1765100648995420593/1562500000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(56784962993921/3057450000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(54016451672167/3057450000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (61149/100000 : ℝ)) (alpha := (56784962993921/3057450000000000 : ℝ)) (beta := (54016451672167/3057450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (61149/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(56784962993921/3057450000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(54016451672167/3057450000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (61149/100000 : ℝ) ^ (89/16 : ℝ) ≤ (202600648995420593/3125000000000000000 : ℝ) := by
    have hpowers : (61149/100000 : ℝ)^89 ≤ (202600648995420593/3125000000000000000 : ℝ)^16 := by
      have hnat : (61149 : ℕ)^89*3125000000000000000^16 ≤ 202600648995420593^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61149 100000 202600648995420593 3125000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61149/100000 : ℝ)) (X := (202600648995420593/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3327600648995420593/3125000000000000000 : ℝ) ≤ (5056784962993921/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3327600648995420593/3125000000000000000 : ℝ)^16 ≤ (5056784962993921/5000000000000000 : ℝ)^89 := by
      have hnat : (3327600648995420593 : ℕ)^16*5000000000000000^89 ≤ 5056784962993921^89*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3327600648995420593 3125000000000000000 5056784962993921 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056784962993921/5000000000000000 : ℝ)) (X := (3327600648995420593/3125000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (1765100648995420593/1562500000000000000 : ℝ) ≤ (638850176833261/625000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (1765100648995420593/1562500000000000000 : ℝ)^16 ≤ (638850176833261/625000000000000 : ℝ)^89 := by
      have hnat : (1765100648995420593 : ℕ)^16*625000000000000^89 ≤ 638850176833261^89*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1765100648995420593 1562500000000000000 638850176833261 625000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (638850176833261/625000000000000 : ℝ)) (X := (1765100648995420593/1562500000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(56784962993921/3057450000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(54016451672167/3057450000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (61149/100000 : ℝ)) (alpha := (56784962993921/3057450000000000 : ℝ)) (beta := (54016451672167/3057450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (61149/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(56784962993921/3057450000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(54016451672167/3057450000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (61149/100000 : ℝ) ^ (89/16 : ℝ) ≤ (202600648995420593/3125000000000000000 : ℝ) := by
    have hpowers : (61149/100000 : ℝ)^89 ≤ (202600648995420593/3125000000000000000 : ℝ)^16 := by
      have hnat : (61149 : ℕ)^89*3125000000000000000^16 ≤ 202600648995420593^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61149 100000 202600648995420593 3125000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61149/100000 : ℝ)) (X := (202600648995420593/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (3327600648995420593/3125000000000000000 : ℝ) ≤ (5056784962993921/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3327600648995420593/3125000000000000000 : ℝ)^16 ≤ (5056784962993921/5000000000000000 : ℝ)^89 := by
      have hnat : (3327600648995420593 : ℕ)^16*5000000000000000^89 ≤ 5056784962993921^89*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3327600648995420593 3125000000000000000 5056784962993921 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056784962993921/5000000000000000 : ℝ)) (X := (3327600648995420593/3125000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1765100648995420593/1562500000000000000 : ℝ) ≤ (638850176833261/625000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (1765100648995420593/1562500000000000000 : ℝ)^16 ≤ (638850176833261/625000000000000 : ℝ)^89 := by
      have hnat : (1765100648995420593 : ℕ)^16*625000000000000^89 ≤ 638850176833261^89*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1765100648995420593 1562500000000000000 638850176833261 625000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (638850176833261/625000000000000 : ℝ)) (X := (1765100648995420593/1562500000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(56784962993921/3057450000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(54016451672167/3057450000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (61149/100000 : ℝ)) (alpha := (56784962993921/3057450000000000 : ℝ)) (beta := (54016451672167/3057450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (61149/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(56784962993921/3057450000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(54016451672167/3057450000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-501815753/5000000000 : ℝ)*X 0 0+(2678721843/5000000000 : ℝ)*X 0 1+(1340828253/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((134082813/250000000 : ℝ)*X 1 0+(-1003631417/10000000000 : ℝ)*X 1 1+(66968053/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5357443823/10000000000 : ℝ)*X 2 0+(1340828257/2500000000 : ℝ)*X 2 1+(-125453911/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-919849417/10000000000 : ℝ)*X 0 0+(1119149161/2500000000 : ℝ)*X 0 1+(6270172571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2820376511/5000000000 : ℝ)*X 1 0+(-40652091/2000000000 : ℝ)*X 1 1+(5572810319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((538743171/1250000000 : ℝ)*X 2 0+(1372288701/2000000000 : ℝ)*X 2 1+(-5033937/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((710519111/2000000000 : ℝ)*X 0 0+(501817821/1000000000 : ℝ)*X 0 1+(176120381/500000000 : ℝ)*X 0 2+(710519111/2000000000 : ℝ)*X 1 0+(501817821/1000000000 : ℝ)*X 1 1+(176120381/500000000 : ℝ)*X 1 2+(710519111/2000000000 : ℝ)*X 2 0+(501817821/1000000000 : ℝ)*X 2 1+(176120381/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-5033937/312500000 : ℝ)*X 0 0+(538743171/1250000000 : ℝ)*X 0 1+(1372288701/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6270172571/10000000000 : ℝ)*X 1 0+(-919849417/10000000000 : ℝ)*X 1 1+(1119149161/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5572810319/10000000000 : ℝ)*X 2 0+(2820376511/5000000000 : ℝ)*X 2 1+(-40652091/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((176120381/500000000 : ℝ)*X 0 0+(710519111/2000000000 : ℝ)*X 0 1+(501817821/1000000000 : ℝ)*X 0 2+(176120381/500000000 : ℝ)*X 1 0+(710519111/2000000000 : ℝ)*X 1 1+(501817821/1000000000 : ℝ)*X 1 2+(176120381/500000000 : ℝ)*X 2 0+(710519111/2000000000 : ℝ)*X 2 1+(501817821/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-40652091/2000000000 : ℝ)*X 0 0+(5572810319/10000000000 : ℝ)*X 0 1+(2820376511/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1372288701/2000000000 : ℝ)*X 1 0+(-5033937/312500000 : ℝ)*X 1 1+(538743171/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1119149161/2500000000 : ℝ)*X 2 0+(6270172571/10000000000 : ℝ)*X 2 1+(-919849417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((501817821/1000000000 : ℝ)*X 0 0+(176120381/500000000 : ℝ)*X 0 1+(710519111/2000000000 : ℝ)*X 0 2+(501817821/1000000000 : ℝ)*X 1 0+(176120381/500000000 : ℝ)*X 1 1+(710519111/2000000000 : ℝ)*X 1 2+(501817821/1000000000 : ℝ)*X 2 0+(176120381/500000000 : ℝ)*X 2 1+(710519111/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327087_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((32203/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32203/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (223130414355817164551/63696875000000000000000000 : ℝ) := by norm_num
    linear_combination (2247333/1000000000000 : ℝ)*(base19) + (99032293739/250000000000 : ℝ)*(base50) + (362907251763/1000000000000 : ℝ)*(base60) + (3750808224739/1000000000000 : ℝ)*(major_s1_0) + (3750808224739/1000000000000 : ℝ)*(major_s1_1) + (3750808224739/1000000000000 : ℝ)*(major_s1_2) + (8386263/500000000000 : ℝ)*(sp_s1_1) + (572910330483/100000000000 : ℝ)*(sp_s1_7) + (572909472623/100000000000 : ℝ)*(sp_s1_8) + (2864546742121/500000000000 : ℝ)*(sp_s1_9) + (886250767857/500000000000 : ℝ)*(sp_s1_13) + (182167/500000000000 : ℝ)*(sp_s1_14) + (403077/40000000000 : ℝ)*(sp_s1_21) + (2532731/125000000000 : ℝ)*(sp_s1_23) + (886250767857/500000000000 : ℝ)*(f.failure) + (5729113746089/1000000000000 : ℝ)*(f.sum) + (935903659919191/1019150000000000000000000000 : ℝ)*base62 + (35504098074301/1528725000000000000000000000 : ℝ)*base64 + (481009130322269/3057450000000000000000000000 : ℝ)*base67 + (2434397007606631/3057450000000000000000000000 : ℝ)*base68 + (77748022282481/254787500000000000000000000 : ℝ)*base71 + (820261341736637/3057450000000000000000000000 : ℝ)*base72 + (3953665171376897/3057450000000000000000000000 : ℝ)*base74 + (3087641840340091/3057450000000000000000000000 : ℝ)*base76 + (56336815320363/127393750000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (37627/50000000000000000 : ℝ)*base87 + (37627/50000000000000000 : ℝ)*base89 + (37627/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((32203/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(32203/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (105002576945454087443/29975000000000000000000000 : ℝ) := by norm_num
    linear_combination (449467/200000000000 : ℝ)*(base21) + (362907251763/1000000000000 : ℝ)*(base40) + (79225834991/200000000000 : ℝ)*(base60) + (3750808224739/1000000000000 : ℝ)*(major_s1_0) + (3750808224739/1000000000000 : ℝ)*(major_s1_1) + (3750808224739/1000000000000 : ℝ)*(major_s1_2) + (1048283/62500000000 : ℝ)*(sp_s1_2) + (2532731/125000000000 : ℝ)*(sp_s1_7) + (403077/40000000000 : ℝ)*(sp_s1_8) + (5729093484241/1000000000000 : ℝ)*(sp_s1_14) + (572910330483/100000000000 : ℝ)*(sp_s1_15) + (5729094726227/1000000000000 : ℝ)*(sp_s1_16) + (886250767857/500000000000 : ℝ)*(sp_s1_20) + (364333/1000000000000 : ℝ)*(sp_s1_22) + (886250767857/500000000000 : ℝ)*(f.failure) + (5729113746089/1000000000000 : ℝ)*(f.sum) + (73109069437057/127393750000000000000000000 : ℝ)*base62 + (421529075162263/3057450000000000000000000000 : ℝ)*base65 + (494894897951933/1528725000000000000000000000 : ℝ)*base66 + (239294412620753/1528725000000000000000000000 : ℝ)*base68 + (66829262021449/1019150000000000000000000000 : ℝ)*base71 + (623368025195279/1528725000000000000000000000 : ℝ)*base73 + (185073977250947/191090625000000000000000000 : ℝ)*base74 + (3145196101594141/3057450000000000000000000000 : ℝ)*base76 + (232907400388579/1019150000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base85 + (37627/50000000000000000 : ℝ)*base87 + (37627/50000000000000000 : ℝ)*base89 + (37627/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32203/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32203/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1785044868455524232369/509575000000000000000000000 : ℝ) := by norm_num
    linear_combination (449467/200000000000 : ℝ)*(base11) + (79225834991/200000000000 : ℝ)*(base40) + (362907251763/1000000000000 : ℝ)*(base50) + (3750808224739/1000000000000 : ℝ)*(major_s1_0) + (3750808224739/1000000000000 : ℝ)*(major_s1_1) + (3750808224739/1000000000000 : ℝ)*(major_s1_2) + (16772523/1000000000000 : ℝ)*(sp_s1_0) + (364333/1000000000000 : ℝ)*(sp_s1_9) + (2532731/125000000000 : ℝ)*(sp_s1_15) + (5038463/500000000000 : ℝ)*(sp_s1_16) + (5729094726231/1000000000000 : ℝ)*(sp_s1_21) + (5729093484241/1000000000000 : ℝ)*(sp_s1_22) + (5729103304831/1000000000000 : ℝ)*(sp_s1_23) + (886250767857/500000000000 : ℝ)*(sp_s1_27) + (886250767857/500000000000 : ℝ)*(f.failure) + (5729113746089/1000000000000 : ℝ)*(f.sum) + (176986170468089/1019150000000000000000000000 : ℝ)*base63 + (442004565257551/1528725000000000000000000000 : ℝ)*base64 + (1762643682996241/3057450000000000000000000000 : ℝ)*base66 + (494894897951933/1528725000000000000000000000 : ℝ)*base68 + (73109069437057/127393750000000000000000000 : ℝ)*base70 + (421529075162263/3057450000000000000000000000 : ℝ)*base73 + (1825819881511877/3057450000000000000000000000 : ℝ)*base74 + (4120294770673291/3057450000000000000000000000 : ℝ)*base76 + (181291004626329/1019150000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (37627/50000000000000000 : ℝ)*base87 + (37627/50000000000000000 : ℝ)*base89 + (37627/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p027_positive87 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  have ho : distinctOrders 87=![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] := by decide
  have hs : ![![true, true, true], ![true, true, true], ![true, true, true]]=(fun (_ _ : Fin 3) => true) := by decide
  have hh := collision_c327087 p hpa (by linarith only [hpb]) X (by simpa only [ho,hs] using hX)
  apply positive_chart_tailratio hX (by decide)
  intro j
  have hn := positive_chart_nonnegative hX j j
  fin_cases j
  · change 0 ≤ pair X 0 0 at hn
    change pair X 0 1 ≤ (2/5:ℝ)*pair X 0 0
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.1,hn]
  · change 0 ≤ pair X 1 1 at hn
    change pair X 1 2 ≤ (2/5:ℝ)*pair X 1 1
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.1,hn]
  · change 0 ≤ pair X 2 2 at hn
    change pair X 2 0 ≤ (2/5:ℝ)*pair X 2 2
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.2,hn]

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_positive87 p hpa hpb X hX

#print axioms solution
