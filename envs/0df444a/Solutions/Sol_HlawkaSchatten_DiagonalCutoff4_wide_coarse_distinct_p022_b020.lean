-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b020
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:49:22.4519+00:00
-- url     : https://prove2.me/submissions/490c970f-2b48-4097-be2b-709dc773cf72

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
theorem collision_support_c322038_s0_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-45271249/625000000 : ℝ)*x 0 + (-4481997981/10000000000 : ℝ)*x 1 + (-652257659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45271249/625000000 : ℝ)^21 ≤ (244103295931/6250000000000 : ℝ)^17 := by
    have hnat : (45271249 : ℕ)^21*6250000000000^17 ≤ 244103295931^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45271249 625000000 244103295931 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481997981/10000000000 : ℝ)^21 ≤ (37107781228439/100000000000000 : ℝ)^17 := by
    have hnat : (4481997981 : ℕ)^21*100000000000000^17 ≤ 37107781228439^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481997981 10000000000 37107781228439 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652257659/1000000000 : ℝ)^21 ≤ (29493283008711/50000000000000 : ℝ)^17 := by
    have hnat : (652257659 : ℕ)^21*50000000000000^17 ≤ 29493283008711^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652257659 1000000000 29493283008711 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45271249/625000000 : ℝ), (-4481997981/10000000000 : ℝ), (-652257659/1000000000 : ℝ)] ![(244103295931/6250000000000 : ℝ), (37107781228439/100000000000000 : ℝ), (29493283008711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45271249/625000000 : ℝ)|^21 ≤ (244103295931/6250000000000 : ℝ)^17
        have hw : |(-45271249/625000000 : ℝ)|=(45271249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4481997981/10000000000 : ℝ)|^21 ≤ (37107781228439/100000000000000 : ℝ)^17
        have hw : |(-4481997981/10000000000 : ℝ)|=(4481997981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-652257659/1000000000 : ℝ)|^21 ≤ (29493283008711/50000000000000 : ℝ)^17
        have hw : |(-652257659/1000000000 : ℝ)|=(652257659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5027077887/10000000000 : ℝ)*x 0 + (4196926431/10000000000 : ℝ)*x 1 + (-3045757019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5027077887/10000000000 : ℝ)^21 ≤ (21379962508399/50000000000000 : ℝ)^17 := by
    have hnat : (5027077887 : ℕ)^21*50000000000000^17 ≤ 21379962508399^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027077887 10000000000 21379962508399 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4196926431/10000000000 : ℝ)^21 ≤ (34214431058121/100000000000000 : ℝ)^17 := by
    have hnat : (4196926431 : ℕ)^21*100000000000000^17 ≤ 34214431058121^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196926431 10000000000 34214431058121 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3045757019/10000000000 : ℝ)^21 ≤ (4605128781639/20000000000000 : ℝ)^17 := by
    have hnat : (3045757019 : ℕ)^21*20000000000000^17 ≤ 4605128781639^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3045757019 10000000000 4605128781639 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5027077887/10000000000 : ℝ), (4196926431/10000000000 : ℝ), (-3045757019/10000000000 : ℝ)] ![(21379962508399/50000000000000 : ℝ), (34214431058121/100000000000000 : ℝ), (4605128781639/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5027077887/10000000000 : ℝ)|^21 ≤ (21379962508399/50000000000000 : ℝ)^17
        have hw : |(5027077887/10000000000 : ℝ)|=(5027077887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4196926431/10000000000 : ℝ)|^21 ≤ (34214431058121/100000000000000 : ℝ)^17
        have hw : |(4196926431/10000000000 : ℝ)|=(4196926431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3045757019/10000000000 : ℝ)|^21 ≤ (4605128781639/20000000000000 : ℝ)^17
        have hw : |(-3045757019/10000000000 : ℝ)|=(3045757019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (157096173/312500000 : ℝ)*x 0 + (-83938533/200000000 : ℝ)*x 1 + (1522878589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (157096173/312500000 : ℝ)^21 ≤ (42759921328731/100000000000000 : ℝ)^17 := by
    have hnat : (157096173 : ℕ)^21*100000000000000^17 ≤ 42759921328731^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157096173 312500000 42759921328731 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83938533/200000000 : ℝ)^21 ≤ (34214433263547/100000000000000 : ℝ)^17 := by
    have hnat : (83938533 : ℕ)^21*100000000000000^17 ≤ 34214433263547^17*200000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83938533 200000000 34214433263547 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1522878589/5000000000 : ℝ)^21 ≤ (460512907861/2000000000000 : ℝ)^17 := by
    have hnat : (1522878589 : ℕ)^21*2000000000000^17 ≤ 460512907861^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522878589 5000000000 460512907861 2000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(157096173/312500000 : ℝ), (-83938533/200000000 : ℝ), (1522878589/5000000000 : ℝ)] ![(42759921328731/100000000000000 : ℝ), (34214433263547/100000000000000 : ℝ), (460512907861/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(157096173/312500000 : ℝ)|^21 ≤ (42759921328731/100000000000000 : ℝ)^17
        have hw : |(157096173/312500000 : ℝ)|=(157096173/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83938533/200000000 : ℝ)|^21 ≤ (34214433263547/100000000000000 : ℝ)^17
        have hw : |(-83938533/200000000 : ℝ)|=(83938533/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1522878589/5000000000 : ℝ)|^21 ≤ (460512907861/2000000000000 : ℝ)^17
        have hw : |(1522878589/5000000000 : ℝ)|=(1522878589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-337318789/5000000000 : ℝ)*x 0 + (-2331059093/5000000000 : ℝ)*x 1 + (-6385956633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337318789/5000000000 : ℝ)^21 ≤ (715463869333/20000000000000 : ℝ)^17 := by
    have hnat : (337318789 : ℕ)^21*20000000000000^17 ≤ 715463869333^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337318789 5000000000 715463869333 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2331059093/5000000000 : ℝ)^21 ≤ (7791711602913/20000000000000 : ℝ)^17 := by
    have hnat : (2331059093 : ℕ)^21*20000000000000^17 ≤ 7791711602913^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2331059093 5000000000 7791711602913 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6385956633/10000000000 : ℝ)^21 ≤ (57464122626693/100000000000000 : ℝ)^17 := by
    have hnat : (6385956633 : ℕ)^21*100000000000000^17 ≤ 57464122626693^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6385956633 10000000000 57464122626693 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-337318789/5000000000 : ℝ), (-2331059093/5000000000 : ℝ), (-6385956633/10000000000 : ℝ)] ![(715463869333/20000000000000 : ℝ), (7791711602913/20000000000000 : ℝ), (57464122626693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-337318789/5000000000 : ℝ)|^21 ≤ (715463869333/20000000000000 : ℝ)^17
        have hw : |(-337318789/5000000000 : ℝ)|=(337318789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2331059093/5000000000 : ℝ)|^21 ≤ (7791711602913/20000000000000 : ℝ)^17
        have hw : |(-2331059093/5000000000 : ℝ)|=(2331059093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6385956633/10000000000 : ℝ)|^21 ≤ (57464122626693/100000000000000 : ℝ)^17
        have hw : |(-6385956633/10000000000 : ℝ)|=(6385956633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1004771291/2000000000 : ℝ)*x 0 + (2273532817/5000000000 : ℝ)*x 1 + (-106492189/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004771291/2000000000 : ℝ)^21 ≤ (42726078972803/100000000000000 : ℝ)^17 := by
    have hnat : (1004771291 : ℕ)^21*100000000000000^17 ≤ 42726078972803^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004771291 2000000000 42726078972803 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273532817/5000000000 : ℝ)^21 ≤ (1888719209821/5000000000000 : ℝ)^17 := by
    have hnat : (2273532817 : ℕ)^21*5000000000000^17 ≤ 1888719209821^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273532817 5000000000 1888719209821 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106492189/400000000 : ℝ)^21 ≤ (76170065681/390625000000 : ℝ)^17 := by
    have hnat : (106492189 : ℕ)^21*390625000000^17 ≤ 76170065681^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106492189 400000000 76170065681 390625000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1004771291/2000000000 : ℝ), (2273532817/5000000000 : ℝ), (-106492189/400000000 : ℝ)] ![(42726078972803/100000000000000 : ℝ), (1888719209821/5000000000000 : ℝ), (76170065681/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1004771291/2000000000 : ℝ)|^21 ≤ (42726078972803/100000000000000 : ℝ)^17
        have hw : |(1004771291/2000000000 : ℝ)|=(1004771291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2273532817/5000000000 : ℝ)|^21 ≤ (1888719209821/5000000000000 : ℝ)^17
        have hw : |(2273532817/5000000000 : ℝ)|=(2273532817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106492189/400000000 : ℝ)|^21 ≤ (76170065681/390625000000 : ℝ)^17
        have hw : |(-106492189/400000000 : ℝ)|=(106492189/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1004771379/2000000000 : ℝ)*x 0 + (-238472097/625000000 : ℝ)*x 1 + (3450022341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004771379/2000000000 : ℝ)^21 ≤ (10681520898831/25000000000000 : ℝ)^17 := by
    have hnat : (1004771379 : ℕ)^21*25000000000000^17 ≤ 10681520898831^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004771379 2000000000 10681520898831 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238472097/625000000 : ℝ)^21 ≤ (6083177694339/20000000000000 : ℝ)^17 := by
    have hnat : (238472097 : ℕ)^21*20000000000000^17 ≤ 6083177694339^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238472097 625000000 6083177694339 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3450022341/10000000000 : ℝ)^21 ≤ (26858027917143/100000000000000 : ℝ)^17 := by
    have hnat : (3450022341 : ℕ)^21*100000000000000^17 ≤ 26858027917143^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3450022341 10000000000 26858027917143 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1004771379/2000000000 : ℝ), (-238472097/625000000 : ℝ), (3450022341/10000000000 : ℝ)] ![(10681520898831/25000000000000 : ℝ), (6083177694339/20000000000000 : ℝ), (26858027917143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1004771379/2000000000 : ℝ)|^21 ≤ (10681520898831/25000000000000 : ℝ)^17
        have hw : |(1004771379/2000000000 : ℝ)|=(1004771379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-238472097/625000000 : ℝ)|^21 ≤ (6083177694339/20000000000000 : ℝ)^17
        have hw : |(-238472097/625000000 : ℝ)|=(238472097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3450022341/10000000000 : ℝ)|^21 ≤ (26858027917143/100000000000000 : ℝ)^17
        have hw : |(3450022341/10000000000 : ℝ)|=(3450022341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7519126747/10000000000 : ℝ)*x 0 + (-1349856763/10000000000 : ℝ)*x 1 + (-2855408099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7519126747/10000000000 : ℝ)^21 ≤ (70312141358721/100000000000000 : ℝ)^17 := by
    have hnat : (7519126747 : ℕ)^21*100000000000000^17 ≤ 70312141358721^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7519126747 10000000000 70312141358721 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349856763/10000000000 : ℝ)^21 ≤ (8426544049981/100000000000000 : ℝ)^17 := by
    have hnat : (1349856763 : ℕ)^21*100000000000000^17 ≤ 8426544049981^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349856763 10000000000 8426544049981 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2855408099/10000000000 : ℝ)^21 ≤ (21261314582859/100000000000000 : ℝ)^17 := by
    have hnat : (2855408099 : ℕ)^21*100000000000000^17 ≤ 21261314582859^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2855408099 10000000000 21261314582859 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7519126747/10000000000 : ℝ), (-1349856763/10000000000 : ℝ), (-2855408099/10000000000 : ℝ)] ![(70312141358721/100000000000000 : ℝ), (8426544049981/100000000000000 : ℝ), (21261314582859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7519126747/10000000000 : ℝ)|^21 ≤ (70312141358721/100000000000000 : ℝ)^17
        have hw : |(7519126747/10000000000 : ℝ)|=(7519126747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1349856763/10000000000 : ℝ)|^21 ≤ (8426544049981/100000000000000 : ℝ)^17
        have hw : |(-1349856763/10000000000 : ℝ)|=(1349856763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2855408099/10000000000 : ℝ)|^21 ≤ (21261314582859/100000000000000 : ℝ)^17
        have hw : |(-2855408099/10000000000 : ℝ)|=(2855408099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-82985009/5000000000 : ℝ)*x 0 + (-4455641651/10000000000 : ℝ)*x 1 + (-683789377/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82985009/5000000000 : ℝ)^21 ≤ (632722219613/100000000000000 : ℝ)^17 := by
    have hnat : (82985009 : ℕ)^21*100000000000000^17 ≤ 632722219613^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82985009 5000000000 632722219613 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4455641651/10000000000 : ℝ)^21 ≤ (4604801527269/12500000000000 : ℝ)^17 := by
    have hnat : (4455641651 : ℕ)^21*12500000000000^17 ≤ 4604801527269^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4455641651 10000000000 4604801527269 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683789377/1000000000 : ℝ)^21 ≤ (6252886555047/10000000000000 : ℝ)^17 := by
    have hnat : (683789377 : ℕ)^21*10000000000000^17 ≤ 6252886555047^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683789377 1000000000 6252886555047 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82985009/5000000000 : ℝ), (-4455641651/10000000000 : ℝ), (-683789377/1000000000 : ℝ)] ![(632722219613/100000000000000 : ℝ), (4604801527269/12500000000000 : ℝ), (6252886555047/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82985009/5000000000 : ℝ)|^21 ≤ (632722219613/100000000000000 : ℝ)^17
        have hw : |(-82985009/5000000000 : ℝ)|=(82985009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4455641651/10000000000 : ℝ)|^21 ≤ (4604801527269/12500000000000 : ℝ)^17
        have hw : |(-4455641651/10000000000 : ℝ)|=(4455641651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-683789377/1000000000 : ℝ)|^21 ≤ (6252886555047/10000000000000 : ℝ)^17
        have hw : |(-683789377/1000000000 : ℝ)|=(683789377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4690662769/10000000000 : ℝ)*x 0 + (3467867/8000000 : ℝ)*x 1 + (-51094473/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4690662769/10000000000 : ℝ)^21 ≤ (9813356207637/25000000000000 : ℝ)^17 := by
    have hnat : (4690662769 : ℕ)^21*25000000000000^17 ≤ 9813356207637^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4690662769 10000000000 9813356207637 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3467867/8000000 : ℝ)^21 ≤ (2225533907179/6250000000000 : ℝ)^17 := by
    have hnat : (3467867 : ℕ)^21*6250000000000^17 ≤ 2225533907179^17*8000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3467867 8000000 2225533907179 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51094473/156250000 : ℝ)^21 ≤ (12569016321967/50000000000000 : ℝ)^17 := by
    have hnat : (51094473 : ℕ)^21*50000000000000^17 ≤ 12569016321967^17*156250000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51094473 156250000 12569016321967 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4690662769/10000000000 : ℝ), (3467867/8000000 : ℝ), (-51094473/156250000 : ℝ)] ![(9813356207637/25000000000000 : ℝ), (2225533907179/6250000000000 : ℝ), (12569016321967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4690662769/10000000000 : ℝ)|^21 ≤ (9813356207637/25000000000000 : ℝ)^17
        have hw : |(4690662769/10000000000 : ℝ)|=(4690662769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3467867/8000000 : ℝ)|^21 ≤ (2225533907179/6250000000000 : ℝ)^17
        have hw : |(3467867/8000000 : ℝ)|=(3467867/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51094473/156250000 : ℝ)|^21 ≤ (12569016321967/50000000000000 : ℝ)^17
        have hw : |(-51094473/156250000 : ℝ)|=(51094473/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (175159311/312500000 : ℝ)*x 0 + (-235486213/625000000 : ℝ)*x 1 + (7105701/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175159311/312500000 : ℝ)^21 ≤ (12228306694693/25000000000000 : ℝ)^17 := by
    have hnat : (175159311 : ℕ)^21*25000000000000^17 ≤ 12228306694693^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175159311 312500000 12228306694693 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235486213/625000000 : ℝ)^21 ≤ (29946141512367/100000000000000 : ℝ)^17 := by
    have hnat : (235486213 : ℕ)^21*100000000000000^17 ≤ 29946141512367^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235486213 625000000 29946141512367 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7105701/25000000 : ℝ)^21 ≤ (10570315850967/50000000000000 : ℝ)^17 := by
    have hnat : (7105701 : ℕ)^21*50000000000000^17 ≤ 10570315850967^17*25000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7105701 25000000 10570315850967 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(175159311/312500000 : ℝ), (-235486213/625000000 : ℝ), (7105701/25000000 : ℝ)] ![(12228306694693/25000000000000 : ℝ), (29946141512367/100000000000000 : ℝ), (10570315850967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(175159311/312500000 : ℝ)|^21 ≤ (12228306694693/25000000000000 : ℝ)^17
        have hw : |(175159311/312500000 : ℝ)|=(175159311/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-235486213/625000000 : ℝ)|^21 ≤ (29946141512367/100000000000000 : ℝ)^17
        have hw : |(-235486213/625000000 : ℝ)|=(235486213/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7105701/25000000 : ℝ)|^21 ≤ (10570315850967/50000000000000 : ℝ)^17
        have hw : |(7105701/25000000 : ℝ)|=(7105701/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_19 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8679541711/10000000000 : ℝ)*x 0 + (-509219239/5000000000 : ℝ)*x 1 + (-156295651/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8679541711/10000000000 : ℝ)^21 ≤ (83950918507697/100000000000000 : ℝ)^17 := by
    have hnat : (8679541711 : ℕ)^21*100000000000000^17 ≤ 83950918507697^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8679541711 10000000000 83950918507697 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509219239/5000000000 : ℝ)^21 ≤ (297493648157/5000000000000 : ℝ)^17 := by
    have hnat : (509219239 : ℕ)^21*5000000000000^17 ≤ 297493648157^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509219239 5000000000 297493648157 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156295651/1000000000 : ℝ)^21 ≤ (10099208521937/100000000000000 : ℝ)^17 := by
    have hnat : (156295651 : ℕ)^21*100000000000000^17 ≤ 10099208521937^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156295651 1000000000 10099208521937 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8679541711/10000000000 : ℝ), (-509219239/5000000000 : ℝ), (-156295651/1000000000 : ℝ)] ![(83950918507697/100000000000000 : ℝ), (297493648157/5000000000000 : ℝ), (10099208521937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8679541711/10000000000 : ℝ)|^21 ≤ (83950918507697/100000000000000 : ℝ)^17
        have hw : |(8679541711/10000000000 : ℝ)|=(8679541711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509219239/5000000000 : ℝ)|^21 ≤ (297493648157/5000000000000 : ℝ)^17
        have hw : |(-509219239/5000000000 : ℝ)|=(509219239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-156295651/1000000000 : ℝ)|^21 ≤ (10099208521937/100000000000000 : ℝ)^17
        have hw : |(-156295651/1000000000 : ℝ)|=(156295651/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-86343443/5000000000 : ℝ)*x 0 + (-4736323369/10000000000 : ℝ)*x 1 + (-41114277/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86343443/5000000000 : ℝ)^21 ≤ (132900571893/20000000000000 : ℝ)^17 := by
    have hnat : (86343443 : ℕ)^21*20000000000000^17 ≤ 132900571893^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86343443 5000000000 132900571893 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4736323369/10000000000 : ℝ)^21 ≤ (39725978545071/100000000000000 : ℝ)^17 := by
    have hnat : (4736323369 : ℕ)^21*100000000000000^17 ≤ 39725978545071^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4736323369 10000000000 39725978545071 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41114277/62500000 : ℝ)^21 ≤ (14902379644053/25000000000000 : ℝ)^17 := by
    have hnat : (41114277 : ℕ)^21*25000000000000^17 ≤ 14902379644053^17*62500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41114277 62500000 14902379644053 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86343443/5000000000 : ℝ), (-4736323369/10000000000 : ℝ), (-41114277/62500000 : ℝ)] ![(132900571893/20000000000000 : ℝ), (39725978545071/100000000000000 : ℝ), (14902379644053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86343443/5000000000 : ℝ)|^21 ≤ (132900571893/20000000000000 : ℝ)^17
        have hw : |(-86343443/5000000000 : ℝ)|=(86343443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4736323369/10000000000 : ℝ)|^21 ≤ (39725978545071/100000000000000 : ℝ)^17
        have hw : |(-4736323369/10000000000 : ℝ)|=(4736323369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41114277/62500000 : ℝ)|^21 ≤ (14902379644053/25000000000000 : ℝ)^17
        have hw : |(-41114277/62500000 : ℝ)|=(41114277/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (699797661/1250000000 : ℝ)*x 0 + (3900154333/10000000000 : ℝ)*x 1 + (-2707365071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (699797661/1250000000 : ℝ)^21 ≤ (48840832231743/100000000000000 : ℝ)^17 := by
    have hnat : (699797661 : ℕ)^21*100000000000000^17 ≤ 48840832231743^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699797661 1250000000 48840832231743 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3900154333/10000000000 : ℝ)^21 ≤ (7812782834657/25000000000000 : ℝ)^17 := by
    have hnat : (3900154333 : ℕ)^21*25000000000000^17 ≤ 7812782834657^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3900154333 10000000000 7812782834657 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707365071/10000000000 : ℝ)^21 ≤ (9954018211703/50000000000000 : ℝ)^17 := by
    have hnat : (2707365071 : ℕ)^21*50000000000000^17 ≤ 9954018211703^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707365071 10000000000 9954018211703 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(699797661/1250000000 : ℝ), (3900154333/10000000000 : ℝ), (-2707365071/10000000000 : ℝ)] ![(48840832231743/100000000000000 : ℝ), (7812782834657/25000000000000 : ℝ), (9954018211703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(699797661/1250000000 : ℝ)|^21 ≤ (48840832231743/100000000000000 : ℝ)^17
        have hw : |(699797661/1250000000 : ℝ)|=(699797661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3900154333/10000000000 : ℝ)|^21 ≤ (7812782834657/25000000000000 : ℝ)^17
        have hw : |(3900154333/10000000000 : ℝ)|=(3900154333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2707365071/10000000000 : ℝ)|^21 ≤ (9954018211703/50000000000000 : ℝ)^17
        have hw : |(-2707365071/10000000000 : ℝ)|=(2707365071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1170144867/2500000000 : ℝ)*x 0 + (-1122053383/2500000000 : ℝ)*x 1 + (1557788681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1170144867/2500000000 : ℝ)^21 ≤ (39149215515507/100000000000000 : ℝ)^17 := by
    have hnat : (1170144867 : ℕ)^21*100000000000000^17 ≤ 39149215515507^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170144867 2500000000 39149215515507 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122053383/2500000000 : ℝ)^21 ≤ (7434272059461/20000000000000 : ℝ)^17 := by
    have hnat : (1122053383 : ℕ)^21*20000000000000^17 ≤ 7434272059461^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122053383 2500000000 7434272059461 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1557788681/5000000000 : ℝ)^21 ≤ (23679424169433/100000000000000 : ℝ)^17 := by
    have hnat : (1557788681 : ℕ)^21*100000000000000^17 ≤ 23679424169433^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557788681 5000000000 23679424169433 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1170144867/2500000000 : ℝ), (-1122053383/2500000000 : ℝ), (1557788681/5000000000 : ℝ)] ![(39149215515507/100000000000000 : ℝ), (7434272059461/20000000000000 : ℝ), (23679424169433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1170144867/2500000000 : ℝ)|^21 ≤ (39149215515507/100000000000000 : ℝ)^17
        have hw : |(1170144867/2500000000 : ℝ)|=(1170144867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1122053383/2500000000 : ℝ)|^21 ≤ (7434272059461/20000000000000 : ℝ)^17
        have hw : |(-1122053383/2500000000 : ℝ)|=(1122053383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1557788681/5000000000 : ℝ)|^21 ≤ (23679424169433/100000000000000 : ℝ)^17
        have hw : |(1557788681/5000000000 : ℝ)|=(1557788681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s0_25 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4354187571/5000000000 : ℝ)*x 0 + (-13300147/125000000 : ℝ)*x 1 + (-147780701/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354187571/5000000000 : ℝ)^21 ≤ (4214777894791/5000000000000 : ℝ)^17 := by
    have hnat : (4354187571 : ℕ)^21*5000000000000^17 ≤ 4214777894791^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354187571 5000000000 4214777894791 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13300147/125000000 : ℝ)^21 ≤ (3140238622109/50000000000000 : ℝ)^17 := by
    have hnat : (13300147 : ℕ)^21*50000000000000^17 ≤ 3140238622109^17*125000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13300147 125000000 3140238622109 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147780701/1000000000 : ℝ)^21 ≤ (471198241827/5000000000000 : ℝ)^17 := by
    have hnat : (147780701 : ℕ)^21*5000000000000^17 ≤ 471198241827^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147780701 1000000000 471198241827 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354187571/5000000000 : ℝ), (-13300147/125000000 : ℝ), (-147780701/1000000000 : ℝ)] ![(4214777894791/5000000000000 : ℝ), (3140238622109/50000000000000 : ℝ), (471198241827/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354187571/5000000000 : ℝ)|^21 ≤ (4214777894791/5000000000000 : ℝ)^17
        have hw : |(4354187571/5000000000 : ℝ)|=(4354187571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13300147/125000000 : ℝ)|^21 ≤ (3140238622109/50000000000000 : ℝ)^17
        have hw : |(-13300147/125000000 : ℝ)|=(13300147/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147780701/1000000000 : ℝ)|^21 ≤ (471198241827/5000000000000 : ℝ)^17
        have hw : |(-147780701/1000000000 : ℝ)|=(147780701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-265307951/1250000000 : ℝ)*x 0 + (-4374711649/10000000000 : ℝ)*x 1 + (-2818065979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265307951/1250000000 : ℝ)^21 ≤ (14738379115699/100000000000000 : ℝ)^17 := by
    have hnat : (265307951 : ℕ)^21*100000000000000^17 ≤ 14738379115699^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265307951 1250000000 14738379115699 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4374711649/10000000000 : ℝ)^21 ≤ (9003408490377/25000000000000 : ℝ)^17 := by
    have hnat : (4374711649 : ℕ)^21*25000000000000^17 ≤ 9003408490377^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374711649 10000000000 9003408490377 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2818065979/5000000000 : ℝ)^21 ≤ (49247986904267/100000000000000 : ℝ)^17 := by
    have hnat : (2818065979 : ℕ)^21*100000000000000^17 ≤ 49247986904267^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2818065979 5000000000 49247986904267 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265307951/1250000000 : ℝ), (-4374711649/10000000000 : ℝ), (-2818065979/5000000000 : ℝ)] ![(14738379115699/100000000000000 : ℝ), (9003408490377/25000000000000 : ℝ), (49247986904267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265307951/1250000000 : ℝ)|^21 ≤ (14738379115699/100000000000000 : ℝ)^17
        have hw : |(-265307951/1250000000 : ℝ)|=(265307951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4374711649/10000000000 : ℝ)|^21 ≤ (9003408490377/25000000000000 : ℝ)^17
        have hw : |(-4374711649/10000000000 : ℝ)|=(4374711649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2818065979/5000000000 : ℝ)|^21 ≤ (49247986904267/100000000000000 : ℝ)^17
        have hw : |(-2818065979/5000000000 : ℝ)|=(2818065979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1176694771/2500000000 : ℝ)*x 0 + (4181654003/10000000000 : ℝ)*x 1 + (-3414747191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1176694771/2500000000 : ℝ)^21 ≤ (2463755864269/6250000000000 : ℝ)^17 := by
    have hnat : (1176694771 : ℕ)^21*6250000000000^17 ≤ 2463755864269^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176694771 2500000000 2463755864269 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4181654003/10000000000 : ℝ)^21 ≤ (681213938619/2000000000000 : ℝ)^17 := by
    have hnat : (4181654003 : ℕ)^21*2000000000000^17 ≤ 681213938619^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181654003 10000000000 681213938619 2000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3414747191/10000000000 : ℝ)^21 ≤ (5303841845087/20000000000000 : ℝ)^17 := by
    have hnat : (3414747191 : ℕ)^21*20000000000000^17 ≤ 5303841845087^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3414747191 10000000000 5303841845087 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1176694771/2500000000 : ℝ), (4181654003/10000000000 : ℝ), (-3414747191/10000000000 : ℝ)] ![(2463755864269/6250000000000 : ℝ), (681213938619/2000000000000 : ℝ), (5303841845087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1176694771/2500000000 : ℝ)|^21 ≤ (2463755864269/6250000000000 : ℝ)^17
        have hw : |(1176694771/2500000000 : ℝ)|=(1176694771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4181654003/10000000000 : ℝ)|^21 ≤ (681213938619/2000000000000 : ℝ)^17
        have hw : |(4181654003/10000000000 : ℝ)|=(4181654003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3414747191/10000000000 : ℝ)|^21 ≤ (5303841845087/20000000000000 : ℝ)^17
        have hw : |(-3414747191/10000000000 : ℝ)|=(3414747191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (941450859/2000000000 : ℝ)*x 0 + (-522672409/1250000000 : ℝ)*x 1 + (853630711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941450859/2000000000 : ℝ)^21 ≤ (1232031572693/3125000000000 : ℝ)^17 := by
    have hnat : (941450859 : ℕ)^21*3125000000000^17 ≤ 1232031572693^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941450859 2000000000 1232031572693 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522672409/1250000000 : ℝ)^21 ≤ (8514483165783/25000000000000 : ℝ)^17 := by
    have hnat : (522672409 : ℕ)^21*25000000000000^17 ≤ 8514483165783^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522672409 1250000000 8514483165783 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (853630711/2500000000 : ℝ)^21 ≤ (5303411398477/20000000000000 : ℝ)^17 := by
    have hnat : (853630711 : ℕ)^21*20000000000000^17 ≤ 5303411398477^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853630711 2500000000 5303411398477 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(941450859/2000000000 : ℝ), (-522672409/1250000000 : ℝ), (853630711/2500000000 : ℝ)] ![(1232031572693/3125000000000 : ℝ), (8514483165783/25000000000000 : ℝ), (5303411398477/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(941450859/2000000000 : ℝ)|^21 ≤ (1232031572693/3125000000000 : ℝ)^17
        have hw : |(941450859/2000000000 : ℝ)|=(941450859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-522672409/1250000000 : ℝ)|^21 ≤ (8514483165783/25000000000000 : ℝ)^17
        have hw : |(-522672409/1250000000 : ℝ)|=(522672409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(853630711/2500000000 : ℝ)|^21 ≤ (5303411398477/20000000000000 : ℝ)^17
        have hw : |(853630711/2500000000 : ℝ)|=(853630711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322038_s1_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (756654267/1250000000 : ℝ)*x 0 + (-2664479191/10000000000 : ℝ)*x 1 + (-3432764837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (756654267/1250000000 : ℝ)^21 ≤ (53788620627379/100000000000000 : ℝ)^17 := by
    have hnat : (756654267 : ℕ)^21*100000000000000^17 ≤ 53788620627379^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756654267 1250000000 53788620627379 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2664479191/10000000000 : ℝ)^21 ≤ (19519212562157/100000000000000 : ℝ)^17 := by
    have hnat : (2664479191 : ℕ)^21*100000000000000^17 ≤ 19519212562157^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2664479191 10000000000 19519212562157 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3432764837/10000000000 : ℝ)^21 ≤ (26692166798267/100000000000000 : ℝ)^17 := by
    have hnat : (3432764837 : ℕ)^21*100000000000000^17 ≤ 26692166798267^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3432764837 10000000000 26692166798267 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(756654267/1250000000 : ℝ), (-2664479191/10000000000 : ℝ), (-3432764837/10000000000 : ℝ)] ![(53788620627379/100000000000000 : ℝ), (19519212562157/100000000000000 : ℝ), (26692166798267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(756654267/1250000000 : ℝ)|^21 ≤ (53788620627379/100000000000000 : ℝ)^17
        have hw : |(756654267/1250000000 : ℝ)|=(756654267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2664479191/10000000000 : ℝ)|^21 ≤ (19519212562157/100000000000000 : ℝ)^17
        have hw : |(-2664479191/10000000000 : ℝ)|=(2664479191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3432764837/10000000000 : ℝ)|^21 ≤ (26692166798267/100000000000000 : ℝ)^17
        have hw : |(-3432764837/10000000000 : ℝ)|=(3432764837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322038 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-45271249/625000000 : ℝ)*X 0 0+(-4481997981/10000000000 : ℝ)*X 0 1+(-652257659/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5027077887/10000000000 : ℝ)*X 1 0+(4196926431/10000000000 : ℝ)*X 1 1+(-3045757019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((157096173/312500000 : ℝ)*X 2 0+(-83938533/200000000 : ℝ)*X 2 1+(1522878589/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-337318789/5000000000 : ℝ)*X 0 0+(-2331059093/5000000000 : ℝ)*X 0 1+(-6385956633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1004771291/2000000000 : ℝ)*X 1 0+(2273532817/5000000000 : ℝ)*X 1 1+(-106492189/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1004771379/2000000000 : ℝ)*X 2 0+(-238472097/625000000 : ℝ)*X 2 1+(3450022341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((7519126747/10000000000 : ℝ)*X 0 0+(-1349856763/10000000000 : ℝ)*X 0 1+(-2855408099/10000000000 : ℝ)*X 0 2+(7519126747/10000000000 : ℝ)*X 1 0+(-1349856763/10000000000 : ℝ)*X 1 1+(-2855408099/10000000000 : ℝ)*X 1 2+(7519126747/10000000000 : ℝ)*X 2 0+(-1349856763/10000000000 : ℝ)*X 2 1+(-2855408099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-82985009/5000000000 : ℝ)*X 0 0+(-4455641651/10000000000 : ℝ)*X 0 1+(-683789377/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4690662769/10000000000 : ℝ)*X 1 0+(3467867/8000000 : ℝ)*X 1 1+(-51094473/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((175159311/312500000 : ℝ)*X 2 0+(-235486213/625000000 : ℝ)*X 2 1+(7105701/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((8679541711/10000000000 : ℝ)*X 0 0+(-509219239/5000000000 : ℝ)*X 0 1+(-156295651/1000000000 : ℝ)*X 0 2+(8679541711/10000000000 : ℝ)*X 1 0+(-509219239/5000000000 : ℝ)*X 1 1+(-156295651/1000000000 : ℝ)*X 1 2+(8679541711/10000000000 : ℝ)*X 2 0+(-509219239/5000000000 : ℝ)*X 2 1+(-156295651/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-86343443/5000000000 : ℝ)*X 0 0+(-4736323369/10000000000 : ℝ)*X 0 1+(-41114277/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((699797661/1250000000 : ℝ)*X 1 0+(3900154333/10000000000 : ℝ)*X 1 1+(-2707365071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1170144867/2500000000 : ℝ)*X 2 0+(-1122053383/2500000000 : ℝ)*X 2 1+(1557788681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((4354187571/5000000000 : ℝ)*X 0 0+(-13300147/125000000 : ℝ)*X 0 1+(-147780701/1000000000 : ℝ)*X 0 2+(4354187571/5000000000 : ℝ)*X 1 0+(-13300147/125000000 : ℝ)*X 1 1+(-147780701/1000000000 : ℝ)*X 1 2+(4354187571/5000000000 : ℝ)*X 2 0+(-13300147/125000000 : ℝ)*X 2 1+(-147780701/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((4893/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4893/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (152001715580916759/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (413139094649/250000000000 : ℝ)*(base39) + (164849453933/250000000000 : ℝ)*(base59) + (4548998607561/1000000000000 : ℝ)*(major_s0_0) + (4548998607561/1000000000000 : ℝ)*(major_s0_1) + (4548998607561/1000000000000 : ℝ)*(major_s0_2) + (50143099/250000000000 : ℝ)*(sp_s0_0) + (22156641/500000000000 : ℝ)*(sp_s0_2) + (6740662505309/1000000000000 : ℝ)*(sp_s0_7) + (6740694079843/1000000000000 : ℝ)*(sp_s0_8) + (269625842087/40000000000 : ℝ)*(sp_s0_9) + (589279056889/250000000000 : ℝ)*(sp_s0_13) + (1284313/100000000000 : ℝ)*(sp_s0_14) + (5682531/31250000000 : ℝ)*(sp_s0_15) + (185555379/1000000000000 : ℝ)*(sp_s0_22) + (589279056889/250000000000 : ℝ)*(f.failure) + (1348175184167/200000000000 : ℝ)*(f.sum) + (347106043663087/1250000000000000000000000000 : ℝ)*base63 + (531524047917047/2000000000000000000000000000 : ℝ)*base65 + (527936189882953/2000000000000000000000000000 : ℝ)*base67 + (21322301836913/2500000000000000000000000000 : ℝ)*base68 + (1672750264762417/10000000000000000000000000000 : ℝ)*base70 + (424397094917047/2000000000000000000000000000 : ℝ)*base73 + (1252103485836913/2500000000000000000000000000 : ℝ)*base74 + (1579051323413087/2500000000000000000000000000 : ℝ)*base77 + (176569361/400000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (1689/2500000000000000 : ℝ)*base86 + (1689/2500000000000000 : ℝ)*base88 + (1689/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7961/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-7961/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23980530948978715184439/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (798699784251/200000000000 : ℝ)*(base39) + (741442279321/500000000000 : ℝ)*(base40) + (137980322709/125000000000 : ℝ)*(base59) + (3689980122303/500000000000 : ℝ)*(major_s0_0) + (3689980122303/500000000000 : ℝ)*(major_s0_1) + (3689980122303/500000000000 : ℝ)*(major_s0_2) + (4637499/25000000000 : ℝ)*(sp_s0_0) + (56143723/200000000000 : ℝ)*(sp_s0_1) + (28340197/200000000000 : ℝ)*(sp_s0_9) + (34230543/500000000000 : ℝ)*(sp_s0_13) + (2733930014569/250000000000 : ℝ)*(sp_s0_14) + (10935624839621/1000000000000 : ℝ)*(sp_s0_15) + (10935763857251/1000000000000 : ℝ)*(sp_s0_16) + (3823943272479/1000000000000 : ℝ)*(sp_s0_19) + (956002933391/250000000000 : ℝ)*(f.failure) + (2733976389559/250000000000 : ℝ)*(f.sum) + (271025741143699/625000000000000000000000000 : ℝ)*base62 + (441977836341119/1000000000000000000000000000 : ℝ)*base64 + (32658510341119/1000000000000000000000000000 : ℝ)*base67 + (445424649081199/1250000000000000000000000000 : ℝ)*base68 + (670077971030391/5000000000000000000000000000 : ℝ)*base70 + (333709102158881/1000000000000000000000000000 : ℝ)*base73 + (440981458206199/1250000000000000000000000000 : ℝ)*base74 + (222835797543801/1250000000000000000000000000 : ℝ)*base77 + (4280737519/10000000000000000000000 : ℝ)*base79 + (2091/2500000000000000 : ℝ)*base86 + (2091/2500000000000000 : ℝ)*base88 + (2091/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31531/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31531/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7246685783959274662761/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1911997051231/500000000000 : ℝ)*(base39) + (992386667349/1000000000000 : ℝ)*(base40) + (1093878044697/1000000000000 : ℝ)*(base59) + (3676426543939/500000000000 : ℝ)*(major_s0_0) + (3676426543939/500000000000 : ℝ)*(major_s0_1) + (3676426543939/500000000000 : ℝ)*(major_s0_2) + (22067839/100000000000 : ℝ)*(sp_s0_7) + (76528649/500000000000 : ℝ)*(sp_s0_8) + (20995611/500000000000 : ℝ)*(sp_s0_16) + (43755271/125000000000 : ℝ)*(sp_s0_19) + (2723878946397/250000000000 : ℝ)*(sp_s0_20) + (272389585167/25000000000 : ℝ)*(sp_s0_21) + (2723923618189/250000000000 : ℝ)*(sp_s0_22) + (119050493897/31250000000 : ℝ)*(sp_s0_25) + (476245730859/125000000000 : ℝ)*(f.failure) + (10895736463979/1000000000000 : ℝ)*(f.sum) + (91986163762587/625000000000000000000000000 : ℝ)*base62 + (432551843276547/1000000000000000000000000000 : ℝ)*base64 + (381248596123453/1000000000000000000000000000 : ℝ)*base66 + (265276294737413/1250000000000000000000000000 : ℝ)*base69 + (2782171943566917/5000000000000000000000000000 : ℝ)*base71 + (427908823876547/1000000000000000000000000000 : ℝ)*base72 + (252177704487413/1250000000000000000000000000 : ℝ)*base75 + (257707539487413/1250000000000000000000000000 : ℝ)*base77 + (96213719/1250000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (341/1250000000000000 : ℝ)*base87 + (341/1250000000000000 : ℝ)*base89 + (341/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (4893/100000 : ℝ) ^ (41/8 : ℝ) ≤ (19234149209227/100000000000000000000 : ℝ) := by
    have hpowers : (4893/100000 : ℝ)^41 ≤ (19234149209227/100000000000000000000 : ℝ)^8 := by
      have hnat : (4893 : ℕ)^41*100000000000000000000^8 ≤ 19234149209227^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4893 100000 19234149209227 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4893/100000 : ℝ)) (X := (19234149209227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100000019234149209227/100000000000000000000 : ℝ) ≤ (2500000093825111/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100000019234149209227/100000000000000000000 : ℝ)^8 ≤ (2500000093825111/2500000000000000 : ℝ)^41 := by
      have hnat : (100000019234149209227 : ℕ)^8*2500000000000000^41 ≤ 2500000093825111^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000019234149209227 100000000000000000000 2500000093825111 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000093825111/2500000000000000 : ℝ)) (X := (100000019234149209227/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50000019234149209227/50000000000000000000 : ℝ) ≤ (10000000750600829/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50000019234149209227/50000000000000000000 : ℝ)^8 ≤ (10000000750600829/10000000000000000 : ℝ)^41 := by
      have hnat : (50000019234149209227 : ℕ)^8*10000000000000000^41 ≤ 10000000750600829^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000019234149209227 50000000000000000000 10000000750600829 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000750600829/10000000000000000 : ℝ)) (X := (50000019234149209227/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(31275037/40775000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(75060077/97860000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (4893/100000 : ℝ)) (alpha := (31275037/40775000000000 : ℝ)) (beta := (75060077/97860000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4893/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(31275037/40775000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(75060077/97860000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7961/25000 : ℝ) ^ (41/8 : ℝ) ≤ (454084325514151/160000000000000000 : ℝ) := by
    have hpowers : (7961/25000 : ℝ)^41 ≤ (454084325514151/160000000000000000 : ℝ)^8 := by
      have hnat : (7961 : ℕ)^41*160000000000000000^8 ≤ 454084325514151^8*25000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7961 25000 454084325514151 160000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7961/25000 : ℝ)) (X := (454084325514151/160000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (160454084325514151/160000000000000000 : ℝ) ≤ (10005531299812869/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (160454084325514151/160000000000000000 : ℝ)^8 ≤ (10005531299812869/10000000000000000 : ℝ)^41 := by
      have hnat : (160454084325514151 : ℕ)^8*10000000000000000^41 ≤ 10005531299812869^41*160000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        160454084325514151 160000000000000000 10005531299812869 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005531299812869/10000000000000000 : ℝ)) (X := (160454084325514151/160000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (80454084325514151/80000000000000000 : ℝ) ≤ (1564226564803/1562500000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (80454084325514151/80000000000000000 : ℝ)^8 ≤ (1564226564803/1562500000000 : ℝ)^41 := by
      have hnat : (80454084325514151 : ℕ)^8*1562500000000^41 ≤ 1564226564803^41*80000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80454084325514151 80000000000000000 1564226564803 1562500000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1564226564803/1562500000000 : ℝ)) (X := (80454084325514151/80000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(5531299812869/3184400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(5518714926331/3184400000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (7961/25000 : ℝ)) (alpha := (5531299812869/3184400000000000 : ℝ)) (beta := (5518714926331/3184400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (7961/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(5531299812869/3184400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(5518714926331/3184400000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (31531/100000 : ℝ) ^ (41/8 : ℝ) ≤ (269793163629482207/100000000000000000000 : ℝ) := by
    have hpowers : (31531/100000 : ℝ)^41 ≤ (269793163629482207/100000000000000000000 : ℝ)^8 := by
      have hnat : (31531 : ℕ)^41*100000000000000000000^8 ≤ 269793163629482207^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31531 100000 269793163629482207 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31531/100000 : ℝ)) (X := (269793163629482207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100269793163629482207/100000000000000000000 : ℝ) ≤ (5002629275214319/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100269793163629482207/100000000000000000000 : ℝ)^8 ≤ (5002629275214319/5000000000000000 : ℝ)^41 := by
      have hnat : (100269793163629482207 : ℕ)^8*5000000000000000^41 ≤ 5002629275214319^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100269793163629482207 100000000000000000000 5002629275214319 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002629275214319/5000000000000000 : ℝ)) (X := (100269793163629482207/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50269793163629482207/50000000000000000000 : ℝ) ≤ (10010505724911871/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50269793163629482207/50000000000000000000 : ℝ)^8 ≤ (10010505724911871/10000000000000000 : ℝ)^41 := by
      have hnat : (50269793163629482207 : ℕ)^8*10000000000000000^41 ≤ 10010505724911871^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50269793163629482207 50000000000000000000 10010505724911871 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010505724911871/10000000000000000 : ℝ)) (X := (50269793163629482207/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(2629275214319/1576550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5247174483233/3153100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (31531/100000 : ℝ)) (alpha := (2629275214319/1576550000000000 : ℝ)) (beta := (5247174483233/3153100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (31531/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(2629275214319/1576550000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5247174483233/3153100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-265307951/1250000000 : ℝ)*X 0 0+(-4374711649/10000000000 : ℝ)*X 0 1+(-2818065979/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1176694771/2500000000 : ℝ)*X 1 0+(4181654003/10000000000 : ℝ)*X 1 1+(-3414747191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((941450859/2000000000 : ℝ)*X 2 0+(-522672409/1250000000 : ℝ)*X 2 1+(853630711/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((756654267/1250000000 : ℝ)*X 0 0+(-2664479191/10000000000 : ℝ)*X 0 1+(-3432764837/10000000000 : ℝ)*X 0 2+(756654267/1250000000 : ℝ)*X 1 0+(-2664479191/10000000000 : ℝ)*X 1 1+(-3432764837/10000000000 : ℝ)*X 1 2+(756654267/1250000000 : ℝ)*X 2 0+(-2664479191/10000000000 : ℝ)*X 2 1+(-3432764837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322038_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-4949824179510171933683562128685921/584872618030000000000000000000000 : ℝ) := by norm_num
    linear_combination (1097/5000000000 : ℝ)*(base12) + (245187/1000000000000 : ℝ)*(base22) + (3119/15625000000 : ℝ)*(base25) + (1107184898273/1000000000000 : ℝ)*(base39) + (241936098793/500000000000 : ℝ)*(base40) + (4537/62500000000 : ℝ)*(base50) + (426122640989/1000000000000 : ℝ)*(base59) + (2823/25000000000 : ℝ)*(ratio_s0_2) + (19299/10000 : ℝ)*(major_s1_0) + (19299/10000 : ℝ)*(major_s1_1) + (19299/10000 : ℝ)*(major_s1_2) + (70525667213/25000000000 : ℝ)*(sp_s1_0) + (35262836349/12500000000 : ℝ)*(sp_s1_1) + (2821026463117/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (35262836349/12500000000 : ℝ)*(f.sum) + (5306517938581209/15688643187500000000000000000 : ℝ)*base62 + (3673747393153/7882750000000000000000000 : ℝ)*base64 + (333849779803/995125000000000000000000 : ℝ)*base66 + (56261860551/985343750000000000000000 : ℝ)*base69 + (433178722285981/918340375000000000000000000 : ℝ)*base70 + (7225736453/29125000000000000000000 : ℝ)*base72 + (617702708617/15922000000000000000000000 : ℝ)*base75 + (187599947251/291250000000000000000000 : ℝ)*base76 + (2305245016211731/4637282500000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p022_b020 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=38 := by omega
  rcases hc with rfl
  · exact collision_c322038 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b020 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
