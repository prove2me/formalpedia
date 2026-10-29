-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b016
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:14:59.482177+00:00
-- url     : https://prove2.me/submissions/98e0b0c6-f7f3-41eb-acdf-98c6c17fe4bf

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
theorem collision_support_c327037_s0_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-761903599/10000000000 : ℝ)*x 0 + (-6713383583/10000000000 : ℝ)*x 1 + (2051986651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (761903599/10000000000 : ℝ)^91 ≤ (1099795755033/25000000000000 : ℝ)^75 := by
    have hnat : (761903599 : ℕ)^91*25000000000000^75 ≤ 1099795755033^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761903599 10000000000 1099795755033 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6713383583/10000000000 : ℝ)^91 ≤ (30831333699439/50000000000000 : ℝ)^75 := by
    have hnat : (6713383583 : ℕ)^91*50000000000000^75 ≤ 30831333699439^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6713383583 10000000000 30831333699439 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2051986651/5000000000 : ℝ)^91 ≤ (1357525982543/4000000000000 : ℝ)^75 := by
    have hnat : (2051986651 : ℕ)^91*4000000000000^75 ≤ 1357525982543^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051986651 5000000000 1357525982543 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-761903599/10000000000 : ℝ), (-6713383583/10000000000 : ℝ), (2051986651/5000000000 : ℝ)] ![(1099795755033/25000000000000 : ℝ), (30831333699439/50000000000000 : ℝ), (1357525982543/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-761903599/10000000000 : ℝ)|^91 ≤ (1099795755033/25000000000000 : ℝ)^75
        have hw : |(-761903599/10000000000 : ℝ)|=(761903599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6713383583/10000000000 : ℝ)|^91 ≤ (30831333699439/50000000000000 : ℝ)^75
        have hw : |(-6713383583/10000000000 : ℝ)|=(6713383583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2051986651/5000000000 : ℝ)|^91 ≤ (1357525982543/4000000000000 : ℝ)^75
        have hw : |(2051986651/5000000000 : ℝ)|=(2051986651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4913684311/10000000000 : ℝ)*x 0 + (378003111/1250000000 : ℝ)*x 1 + (2072205447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4913684311/10000000000 : ℝ)^91 ≤ (42225434890031/100000000000000 : ℝ)^75 := by
    have hnat : (4913684311 : ℕ)^91*100000000000000^75 ≤ 42225434890031^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4913684311 10000000000 42225434890031 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378003111/1250000000 : ℝ)^91 ≤ (937209961813/4000000000000 : ℝ)^75 := by
    have hnat : (378003111 : ℕ)^91*4000000000000^75 ≤ 937209961813^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378003111 1250000000 937209961813 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072205447/5000000000 : ℝ)^91 ≤ (2146519753083/6250000000000 : ℝ)^75 := by
    have hnat : (2072205447 : ℕ)^91*6250000000000^75 ≤ 2146519753083^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072205447 5000000000 2146519753083 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4913684311/10000000000 : ℝ), (378003111/1250000000 : ℝ), (2072205447/5000000000 : ℝ)] ![(42225434890031/100000000000000 : ℝ), (937209961813/4000000000000 : ℝ), (2146519753083/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4913684311/10000000000 : ℝ)|^91 ≤ (42225434890031/100000000000000 : ℝ)^75
        have hw : |(4913684311/10000000000 : ℝ)|=(4913684311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(378003111/1250000000 : ℝ)|^91 ≤ (937209961813/4000000000000 : ℝ)^75
        have hw : |(378003111/1250000000 : ℝ)|=(378003111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072205447/5000000000 : ℝ)|^91 ≤ (2146519753083/6250000000000 : ℝ)^75
        have hw : |(2072205447/5000000000 : ℝ)|=(2072205447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1616040067/2000000000 : ℝ)*x 0 + (-1264809069/10000000000 : ℝ)*x 1 + (2053932371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1616040067/2000000000 : ℝ)^91 ≤ (77209756462823/100000000000000 : ℝ)^75 := by
    have hnat : (1616040067 : ℕ)^91*100000000000000^75 ≤ 77209756462823^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616040067 2000000000 77209756462823 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1264809069/10000000000 : ℝ)^91 ≤ (325474490679/4000000000000 : ℝ)^75 := by
    have hnat : (1264809069 : ℕ)^91*4000000000000^75 ≤ 325474490679^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264809069 10000000000 325474490679 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2053932371/10000000000 : ℝ)^91 ≤ (7326690629579/50000000000000 : ℝ)^75 := by
    have hnat : (2053932371 : ℕ)^91*50000000000000^75 ≤ 7326690629579^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053932371 10000000000 7326690629579 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1616040067/2000000000 : ℝ), (-1264809069/10000000000 : ℝ), (2053932371/10000000000 : ℝ)] ![(77209756462823/100000000000000 : ℝ), (325474490679/4000000000000 : ℝ), (7326690629579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1616040067/2000000000 : ℝ)|^91 ≤ (77209756462823/100000000000000 : ℝ)^75
        have hw : |(1616040067/2000000000 : ℝ)|=(1616040067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1264809069/10000000000 : ℝ)|^91 ≤ (325474490679/4000000000000 : ℝ)^75
        have hw : |(-1264809069/10000000000 : ℝ)|=(1264809069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2053932371/10000000000 : ℝ)|^91 ≤ (7326690629579/50000000000000 : ℝ)^75
        have hw : |(2053932371/10000000000 : ℝ)|=(2053932371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-393287507/5000000000 : ℝ)*x 0 + (-1378950003/2000000000 : ℝ)*x 1 + (3883385079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393287507/5000000000 : ℝ)^91 ≤ (4572615785843/100000000000000 : ℝ)^75 := by
    have hnat : (393287507 : ℕ)^91*100000000000000^75 ≤ 4572615785843^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393287507 5000000000 4572615785843 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378950003/2000000000 : ℝ)^91 ≤ (63689691169633/100000000000000 : ℝ)^75 := by
    have hnat : (1378950003 : ℕ)^91*100000000000000^75 ≤ 63689691169633^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378950003 2000000000 63689691169633 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3883385079/10000000000 : ℝ)^91 ≤ (31737693025687/100000000000000 : ℝ)^75 := by
    have hnat : (3883385079 : ℕ)^91*100000000000000^75 ≤ 31737693025687^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3883385079 10000000000 31737693025687 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393287507/5000000000 : ℝ), (-1378950003/2000000000 : ℝ), (3883385079/10000000000 : ℝ)] ![(4572615785843/100000000000000 : ℝ), (63689691169633/100000000000000 : ℝ), (31737693025687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393287507/5000000000 : ℝ)|^91 ≤ (4572615785843/100000000000000 : ℝ)^75
        have hw : |(-393287507/5000000000 : ℝ)|=(393287507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1378950003/2000000000 : ℝ)|^91 ≤ (63689691169633/100000000000000 : ℝ)^75
        have hw : |(-1378950003/2000000000 : ℝ)|=(1378950003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3883385079/10000000000 : ℝ)|^91 ≤ (31737693025687/100000000000000 : ℝ)^75
        have hw : |(3883385079/10000000000 : ℝ)|=(3883385079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4859544111/10000000000 : ℝ)*x 0 + (3054033451/10000000000 : ℝ)*x 1 + (2086190327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4859544111/10000000000 : ℝ)^91 ≤ (41661596472681/100000000000000 : ℝ)^75 := by
    have hnat : (4859544111 : ℕ)^91*100000000000000^75 ≤ 41661596472681^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4859544111 10000000000 41661596472681 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3054033451/10000000000 : ℝ)^91 ≤ (23712655837201/100000000000000 : ℝ)^75 := by
    have hnat : (3054033451 : ℕ)^91*100000000000000^75 ≤ 23712655837201^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3054033451 10000000000 23712655837201 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086190327/5000000000 : ℝ)^91 ≤ (17312873839807/50000000000000 : ℝ)^75 := by
    have hnat : (2086190327 : ℕ)^91*50000000000000^75 ≤ 17312873839807^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086190327 5000000000 17312873839807 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4859544111/10000000000 : ℝ), (3054033451/10000000000 : ℝ), (2086190327/5000000000 : ℝ)] ![(41661596472681/100000000000000 : ℝ), (23712655837201/100000000000000 : ℝ), (17312873839807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4859544111/10000000000 : ℝ)|^91 ≤ (41661596472681/100000000000000 : ℝ)^75
        have hw : |(4859544111/10000000000 : ℝ)|=(4859544111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3054033451/10000000000 : ℝ)|^91 ≤ (23712655837201/100000000000000 : ℝ)^75
        have hw : |(3054033451/10000000000 : ℝ)|=(3054033451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086190327/5000000000 : ℝ)|^91 ≤ (17312873839807/50000000000000 : ℝ)^75
        have hw : |(2086190327/5000000000 : ℝ)|=(2086190327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4859543921/10000000000 : ℝ)*x 0 + (-1466074411/5000000000 : ℝ)*x 1 + (-4285600333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4859543921/10000000000 : ℝ)^91 ≤ (8332318899257/20000000000000 : ℝ)^75 := by
    have hnat : (4859543921 : ℕ)^91*20000000000000^75 ≤ 8332318899257^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4859543921 10000000000 8332318899257 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1466074411/5000000000 : ℝ)^91 ≤ (22569348599263/100000000000000 : ℝ)^75 := by
    have hnat : (1466074411 : ℕ)^91*100000000000000^75 ≤ 22569348599263^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1466074411 5000000000 22569348599263 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4285600333/10000000000 : ℝ)^91 ≤ (17884528445637/50000000000000 : ℝ)^75 := by
    have hnat : (4285600333 : ℕ)^91*50000000000000^75 ≤ 17884528445637^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285600333 10000000000 17884528445637 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4859543921/10000000000 : ℝ), (-1466074411/5000000000 : ℝ), (-4285600333/10000000000 : ℝ)] ![(8332318899257/20000000000000 : ℝ), (22569348599263/100000000000000 : ℝ), (17884528445637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4859543921/10000000000 : ℝ)|^91 ≤ (8332318899257/20000000000000 : ℝ)^75
        have hw : |(4859543921/10000000000 : ℝ)|=(4859543921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1466074411/5000000000 : ℝ)|^91 ≤ (22569348599263/100000000000000 : ℝ)^75
        have hw : |(-1466074411/5000000000 : ℝ)|=(1466074411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4285600333/10000000000 : ℝ)|^91 ≤ (17884528445637/50000000000000 : ℝ)^75
        have hw : |(-4285600333/10000000000 : ℝ)|=(4285600333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (815885477/1000000000 : ℝ)*x 0 + (-137638539/2000000000 : ℝ)*x 1 + (1216094677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (815885477/1000000000 : ℝ)^91 ≤ (78122613893593/100000000000000 : ℝ)^75 := by
    have hnat : (815885477 : ℕ)^91*100000000000000^75 ≤ 78122613893593^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815885477 1000000000 78122613893593 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137638539/2000000000 : ℝ)^91 ≤ (3888256179039/100000000000000 : ℝ)^75 := by
    have hnat : (137638539 : ℕ)^91*100000000000000^75 ≤ 3888256179039^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137638539 2000000000 3888256179039 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216094677/5000000000 : ℝ)^91 ≤ (17989129916759/100000000000000 : ℝ)^75 := by
    have hnat : (1216094677 : ℕ)^91*100000000000000^75 ≤ 17989129916759^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216094677 5000000000 17989129916759 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(815885477/1000000000 : ℝ), (-137638539/2000000000 : ℝ), (1216094677/5000000000 : ℝ)] ![(78122613893593/100000000000000 : ℝ), (3888256179039/100000000000000 : ℝ), (17989129916759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(815885477/1000000000 : ℝ)|^91 ≤ (78122613893593/100000000000000 : ℝ)^75
        have hw : |(815885477/1000000000 : ℝ)|=(815885477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137638539/2000000000 : ℝ)|^91 ≤ (3888256179039/100000000000000 : ℝ)^75
        have hw : |(-137638539/2000000000 : ℝ)|=(137638539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1216094677/5000000000 : ℝ)|^91 ≤ (17989129916759/100000000000000 : ℝ)^75
        have hw : |(1216094677/5000000000 : ℝ)|=(1216094677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-50708953/1000000000 : ℝ)*x 0 + (-6661749737/10000000000 : ℝ)*x 1 + (216543253/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50708953/1000000000 : ℝ)^91 ≤ (134216539937/5000000000000 : ℝ)^75 := by
    have hnat : (50708953 : ℕ)^91*5000000000000^75 ≤ 134216539937^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50708953 1000000000 134216539937 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6661749737/10000000000 : ℝ)^91 ≤ (119311926813/195312500000 : ℝ)^75 := by
    have hnat : (6661749737 : ℕ)^91*195312500000^75 ≤ 119311926813^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6661749737 10000000000 119311926813 195312500000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216543253/500000000 : ℝ)^91 ≤ (3622796266127/10000000000000 : ℝ)^75 := by
    have hnat : (216543253 : ℕ)^91*10000000000000^75 ≤ 3622796266127^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216543253 500000000 3622796266127 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50708953/1000000000 : ℝ), (-6661749737/10000000000 : ℝ), (216543253/500000000 : ℝ)] ![(134216539937/5000000000000 : ℝ), (119311926813/195312500000 : ℝ), (3622796266127/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50708953/1000000000 : ℝ)|^91 ≤ (134216539937/5000000000000 : ℝ)^75
        have hw : |(-50708953/1000000000 : ℝ)|=(50708953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6661749737/10000000000 : ℝ)|^91 ≤ (119311926813/195312500000 : ℝ)^75
        have hw : |(-6661749737/10000000000 : ℝ)|=(6661749737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216543253/500000000 : ℝ)|^91 ≤ (3622796266127/10000000000000 : ℝ)^75
        have hw : |(216543253/500000000 : ℝ)|=(216543253/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (240477437/500000000 : ℝ)*x 0 + (3060886637/10000000000 : ℝ)*x 1 + (421750669/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240477437/500000000 : ℝ)^91 ≤ (41142112495951/100000000000000 : ℝ)^75 := by
    have hnat : (240477437 : ℕ)^91*100000000000000^75 ≤ 41142112495951^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240477437 500000000 41142112495951 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3060886637/10000000000 : ℝ)^91 ≤ (2972154198869/12500000000000 : ℝ)^75 := by
    have hnat : (3060886637 : ℕ)^91*12500000000000^75 ≤ 2972154198869^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3060886637 10000000000 2972154198869 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421750669/1000000000 : ℝ)^91 ≤ (35080653895957/100000000000000 : ℝ)^75 := by
    have hnat : (421750669 : ℕ)^91*100000000000000^75 ≤ 35080653895957^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421750669 1000000000 35080653895957 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(240477437/500000000 : ℝ), (3060886637/10000000000 : ℝ), (421750669/1000000000 : ℝ)] ![(41142112495951/100000000000000 : ℝ), (2972154198869/12500000000000 : ℝ), (35080653895957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(240477437/500000000 : ℝ)|^91 ≤ (41142112495951/100000000000000 : ℝ)^75
        have hw : |(240477437/500000000 : ℝ)|=(240477437/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3060886637/10000000000 : ℝ)|^91 ≤ (2972154198869/12500000000000 : ℝ)^75
        have hw : |(3060886637/10000000000 : ℝ)|=(3060886637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(421750669/1000000000 : ℝ)|^91 ≤ (35080653895957/100000000000000 : ℝ)^75
        have hw : |(421750669/1000000000 : ℝ)|=(421750669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_16 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (103420183/200000000 : ℝ)*x 0 + (-2850064593/10000000000 : ℝ)*x 1 + (-1009358791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103420183/200000000 : ℝ)^91 ≤ (22461635527849/50000000000000 : ℝ)^75 := by
    have hnat : (103420183 : ℕ)^91*50000000000000^75 ≤ 22461635527849^75*200000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103420183 200000000 22461635527849 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2850064593/10000000000 : ℝ)^91 ≤ (10902523809467/50000000000000 : ℝ)^75 := by
    have hnat : (2850064593 : ℕ)^91*50000000000000^75 ≤ 10902523809467^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850064593 10000000000 10902523809467 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009358791/2500000000 : ℝ)^91 ≤ (16635840656869/50000000000000 : ℝ)^75 := by
    have hnat : (1009358791 : ℕ)^91*50000000000000^75 ≤ 16635840656869^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009358791 2500000000 16635840656869 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103420183/200000000 : ℝ), (-2850064593/10000000000 : ℝ), (-1009358791/2500000000 : ℝ)] ![(22461635527849/50000000000000 : ℝ), (10902523809467/50000000000000 : ℝ), (16635840656869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103420183/200000000 : ℝ)|^91 ≤ (22461635527849/50000000000000 : ℝ)^75
        have hw : |(103420183/200000000 : ℝ)|=(103420183/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2850064593/10000000000 : ℝ)|^91 ≤ (10902523809467/50000000000000 : ℝ)^75
        have hw : |(-2850064593/10000000000 : ℝ)|=(2850064593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1009358791/2500000000 : ℝ)|^91 ≤ (16635840656869/50000000000000 : ℝ)^75
        have hw : |(-1009358791/2500000000 : ℝ)|=(1009358791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1684763009/2000000000 : ℝ)*x 0 + (-299533973/2500000000 : ℝ)*x 1 + (821051881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1684763009/2000000000 : ℝ)^91 ≤ (81211470002709/100000000000000 : ℝ)^75 := by
    have hnat : (1684763009 : ℕ)^91*100000000000000^75 ≤ 81211470002709^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684763009 2000000000 81211470002709 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299533973/2500000000 : ℝ)^91 ≤ (3809699427911/50000000000000 : ℝ)^75 := by
    have hnat : (299533973 : ℕ)^91*50000000000000^75 ≤ 3809699427911^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299533973 2500000000 3809699427911 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (821051881/5000000000 : ℝ)^91 ≤ (11169131132961/100000000000000 : ℝ)^75 := by
    have hnat : (821051881 : ℕ)^91*100000000000000^75 ≤ 11169131132961^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821051881 5000000000 11169131132961 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1684763009/2000000000 : ℝ), (-299533973/2500000000 : ℝ), (821051881/5000000000 : ℝ)] ![(81211470002709/100000000000000 : ℝ), (3809699427911/50000000000000 : ℝ), (11169131132961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1684763009/2000000000 : ℝ)|^91 ≤ (81211470002709/100000000000000 : ℝ)^75
        have hw : |(1684763009/2000000000 : ℝ)|=(1684763009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299533973/2500000000 : ℝ)|^91 ≤ (3809699427911/50000000000000 : ℝ)^75
        have hw : |(-299533973/2500000000 : ℝ)|=(299533973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(821051881/5000000000 : ℝ)|^91 ≤ (11169131132961/100000000000000 : ℝ)^75
        have hw : |(821051881/5000000000 : ℝ)|=(821051881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-286940209/5000000000 : ℝ)*x 0 + (-6871555689/10000000000 : ℝ)*x 1 + (162214531/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (286940209/5000000000 : ℝ)^91 ≤ (1559576360093/50000000000000 : ℝ)^75 := by
    have hnat : (286940209 : ℕ)^91*50000000000000^75 ≤ 1559576360093^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286940209 5000000000 1559576360093 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6871555689/10000000000 : ℝ)^91 ≤ (63429820958247/100000000000000 : ℝ)^75 := by
    have hnat : (6871555689 : ℕ)^91*100000000000000^75 ≤ 63429820958247^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6871555689 10000000000 63429820958247 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162214531/400000000 : ℝ)^91 ≤ (33451026309763/100000000000000 : ℝ)^75 := by
    have hnat : (162214531 : ℕ)^91*100000000000000^75 ≤ 33451026309763^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162214531 400000000 33451026309763 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-286940209/5000000000 : ℝ), (-6871555689/10000000000 : ℝ), (162214531/400000000 : ℝ)] ![(1559576360093/50000000000000 : ℝ), (63429820958247/100000000000000 : ℝ), (33451026309763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-286940209/5000000000 : ℝ)|^91 ≤ (1559576360093/50000000000000 : ℝ)^75
        have hw : |(-286940209/5000000000 : ℝ)|=(286940209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6871555689/10000000000 : ℝ)|^91 ≤ (63429820958247/100000000000000 : ℝ)^75
        have hw : |(-6871555689/10000000000 : ℝ)|=(6871555689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162214531/400000000 : ℝ)|^91 ≤ (33451026309763/100000000000000 : ℝ)^75
        have hw : |(162214531/400000000 : ℝ)|=(162214531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_22 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2552109101/5000000000 : ℝ)*x 0 + (742262709/2500000000 : ℝ)*x 1 + (1998376331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2552109101/5000000000 : ℝ)^91 ≤ (44220210070933/100000000000000 : ℝ)^75 := by
    have hnat : (2552109101 : ℕ)^91*100000000000000^75 ≤ 44220210070933^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2552109101 5000000000 44220210070933 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (742262709/2500000000 : ℝ)^91 ≤ (2291444777603/10000000000000 : ℝ)^75 := by
    have hnat : (742262709 : ℕ)^91*10000000000000^75 ≤ 2291444777603^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742262709 2500000000 2291444777603 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1998376331/5000000000 : ℝ)^91 ≤ (1314613685517/4000000000000 : ℝ)^75 := by
    have hnat : (1998376331 : ℕ)^91*4000000000000^75 ≤ 1314613685517^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998376331 5000000000 1314613685517 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2552109101/5000000000 : ℝ), (742262709/2500000000 : ℝ), (1998376331/5000000000 : ℝ)] ![(44220210070933/100000000000000 : ℝ), (2291444777603/10000000000000 : ℝ), (1314613685517/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2552109101/5000000000 : ℝ)|^91 ≤ (44220210070933/100000000000000 : ℝ)^75
        have hw : |(2552109101/5000000000 : ℝ)|=(2552109101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(742262709/2500000000 : ℝ)|^91 ≤ (2291444777603/10000000000000 : ℝ)^75
        have hw : |(742262709/2500000000 : ℝ)|=(742262709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1998376331/5000000000 : ℝ)|^91 ≤ (1314613685517/4000000000000 : ℝ)^75
        have hw : |(1998376331/5000000000 : ℝ)|=(1998376331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_23 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (958806533/2000000000 : ℝ)*x 0 + (-3017131789/10000000000 : ℝ)*x 1 + (-427417757/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (958806533/2000000000 : ℝ)^91 ≤ (2049056203471/5000000000000 : ℝ)^75 := by
    have hnat : (958806533 : ℕ)^91*5000000000000^75 ≤ 2049056203471^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958806533 2000000000 2049056203471 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3017131789/10000000000 : ℝ)^91 ≤ (4673092628423/20000000000000 : ℝ)^75 := by
    have hnat : (3017131789 : ℕ)^91*20000000000000^75 ≤ 4673092628423^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017131789 10000000000 4673092628423 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427417757/1000000000 : ℝ)^91 ≤ (35653412775387/100000000000000 : ℝ)^75 := by
    have hnat : (427417757 : ℕ)^91*100000000000000^75 ≤ 35653412775387^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427417757 1000000000 35653412775387 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(958806533/2000000000 : ℝ), (-3017131789/10000000000 : ℝ), (-427417757/1000000000 : ℝ)] ![(2049056203471/5000000000000 : ℝ), (4673092628423/20000000000000 : ℝ), (35653412775387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(958806533/2000000000 : ℝ)|^91 ≤ (2049056203471/5000000000000 : ℝ)^75
        have hw : |(958806533/2000000000 : ℝ)|=(958806533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3017131789/10000000000 : ℝ)|^91 ≤ (4673092628423/20000000000000 : ℝ)^75
        have hw : |(-3017131789/10000000000 : ℝ)|=(3017131789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427417757/1000000000 : ℝ)|^91 ≤ (35653412775387/100000000000000 : ℝ)^75
        have hw : |(-427417757/1000000000 : ℝ)|=(427417757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s0_27 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (423698403/500000000 : ℝ)*x 0 + (-763162289/10000000000 : ℝ)*x 1 + (1954071327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423698403/500000000 : ℝ)^91 ≤ (16359700193947/20000000000000 : ℝ)^75 := by
    have hnat : (423698403 : ℕ)^91*20000000000000^75 ≤ 16359700193947^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423698403 500000000 16359700193947 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (763162289/10000000000 : ℝ)^91 ≤ (176320103601/4000000000000 : ℝ)^75 := by
    have hnat : (763162289 : ℕ)^91*4000000000000^75 ≤ 176320103601^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763162289 10000000000 176320103601 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1954071327/10000000000 : ℝ)^91 ≤ (215523381699/1562500000000 : ℝ)^75 := by
    have hnat : (1954071327 : ℕ)^91*1562500000000^75 ≤ 215523381699^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954071327 10000000000 215523381699 1562500000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423698403/500000000 : ℝ), (-763162289/10000000000 : ℝ), (1954071327/10000000000 : ℝ)] ![(16359700193947/20000000000000 : ℝ), (176320103601/4000000000000 : ℝ), (215523381699/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423698403/500000000 : ℝ)|^91 ≤ (16359700193947/20000000000000 : ℝ)^75
        have hw : |(423698403/500000000 : ℝ)|=(423698403/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-763162289/10000000000 : ℝ)|^91 ≤ (176320103601/4000000000000 : ℝ)^75
        have hw : |(-763162289/10000000000 : ℝ)|=(763162289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1954071327/10000000000 : ℝ)|^91 ≤ (215523381699/1562500000000 : ℝ)^75
        have hw : |(1954071327/10000000000 : ℝ)|=(1954071327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s1_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-975879277/5000000000 : ℝ)*x 0 + (-563833087/1000000000 : ℝ)*x 1 + (108524523/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975879277/5000000000 : ℝ)^91 ≤ (13773690635393/100000000000000 : ℝ)^75 := by
    have hnat : (975879277 : ℕ)^91*100000000000000^75 ≤ 13773690635393^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975879277 5000000000 13773690635393 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563833087/1000000000 : ℝ)^91 ≤ (49895649080809/100000000000000 : ℝ)^75 := by
    have hnat : (563833087 : ℕ)^91*100000000000000^75 ≤ 49895649080809^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563833087 1000000000 49895649080809 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108524523/250000000 : ℝ)^91 ≤ (36330660267817/100000000000000 : ℝ)^75 := by
    have hnat : (108524523 : ℕ)^91*100000000000000^75 ≤ 36330660267817^75*250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108524523 250000000 36330660267817 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975879277/5000000000 : ℝ), (-563833087/1000000000 : ℝ), (108524523/250000000 : ℝ)] ![(13773690635393/100000000000000 : ℝ), (49895649080809/100000000000000 : ℝ), (36330660267817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975879277/5000000000 : ℝ)|^91 ≤ (13773690635393/100000000000000 : ℝ)^75
        have hw : |(-975879277/5000000000 : ℝ)|=(975879277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-563833087/1000000000 : ℝ)|^91 ≤ (49895649080809/100000000000000 : ℝ)^75
        have hw : |(-563833087/1000000000 : ℝ)|=(563833087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108524523/250000000 : ℝ)|^91 ≤ (36330660267817/100000000000000 : ℝ)^75
        have hw : |(108524523/250000000 : ℝ)|=(108524523/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s1_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4695648273/10000000000 : ℝ)*x 0 + (25956341/78125000 : ℝ)*x 1 + (2043749167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4695648273/10000000000 : ℝ)^91 ≤ (9990731477741/25000000000000 : ℝ)^75 := by
    have hnat : (4695648273 : ℕ)^91*25000000000000^75 ≤ 9990731477741^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4695648273 10000000000 9990731477741 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25956341/78125000 : ℝ)^91 ≤ (2626415955303/10000000000000 : ℝ)^75 := by
    have hnat : (25956341 : ℕ)^91*10000000000000^75 ≤ 2626415955303^75*78125000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25956341 78125000 2626415955303 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2043749167/5000000000 : ℝ)^91 ≤ (6754582905529/20000000000000 : ℝ)^75 := by
    have hnat : (2043749167 : ℕ)^91*20000000000000^75 ≤ 6754582905529^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043749167 5000000000 6754582905529 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4695648273/10000000000 : ℝ), (25956341/78125000 : ℝ), (2043749167/5000000000 : ℝ)] ![(9990731477741/25000000000000 : ℝ), (2626415955303/10000000000000 : ℝ), (6754582905529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4695648273/10000000000 : ℝ)|^91 ≤ (9990731477741/25000000000000 : ℝ)^75
        have hw : |(4695648273/10000000000 : ℝ)|=(4695648273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25956341/78125000 : ℝ)|^91 ≤ (2626415955303/10000000000000 : ℝ)^75
        have hw : |(25956341/78125000 : ℝ)|=(25956341/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2043749167/5000000000 : ℝ)|^91 ≤ (6754582905529/20000000000000 : ℝ)^75
        have hw : |(2043749167/5000000000 : ℝ)|=(2043749167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s1_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (938778219/2000000000 : ℝ)*x 0 + (-415404897/1250000000 : ℝ)*x 1 + (-511064553/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (938778219/2000000000 : ℝ)^91 ≤ (39944781608877/100000000000000 : ℝ)^75 := by
    have hnat : (938778219 : ℕ)^91*100000000000000^75 ≤ 39944781608877^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938778219 2000000000 39944781608877 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415404897/1250000000 : ℝ)^91 ≤ (26272097065691/100000000000000 : ℝ)^75 := by
    have hnat : (415404897 : ℕ)^91*100000000000000^75 ≤ 26272097065691^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415404897 1250000000 26272097065691 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511064553/1250000000 : ℝ)^91 ≤ (16891560654249/50000000000000 : ℝ)^75 := by
    have hnat : (511064553 : ℕ)^91*50000000000000^75 ≤ 16891560654249^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511064553 1250000000 16891560654249 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(938778219/2000000000 : ℝ), (-415404897/1250000000 : ℝ), (-511064553/1250000000 : ℝ)] ![(39944781608877/100000000000000 : ℝ), (26272097065691/100000000000000 : ℝ), (16891560654249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(938778219/2000000000 : ℝ)|^91 ≤ (39944781608877/100000000000000 : ℝ)^75
        have hw : |(938778219/2000000000 : ℝ)|=(938778219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415404897/1250000000 : ℝ)|^91 ≤ (26272097065691/100000000000000 : ℝ)^75
        have hw : |(-415404897/1250000000 : ℝ)|=(415404897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511064553/1250000000 : ℝ)|^91 ≤ (16891560654249/50000000000000 : ℝ)^75
        have hw : |(-511064553/1250000000 : ℝ)|=(511064553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327037_s1_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6223784877/10000000000 : ℝ)*x 0 + (-128931971/400000000 : ℝ)*x 1 + (2481635253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6223784877/10000000000 : ℝ)^91 ≤ (14062403565603/25000000000000 : ℝ)^75 := by
    have hnat : (6223784877 : ℕ)^91*25000000000000^75 ≤ 14062403565603^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6223784877 10000000000 14062403565603 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128931971/400000000 : ℝ)^91 ≤ (25316564159127/100000000000000 : ℝ)^75 := by
    have hnat : (128931971 : ℕ)^91*100000000000000^75 ≤ 25316564159127^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128931971 400000000 25316564159127 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2481635253/10000000000 : ℝ)^91 ≤ (9216910780647/50000000000000 : ℝ)^75 := by
    have hnat : (2481635253 : ℕ)^91*50000000000000^75 ≤ 9216910780647^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2481635253 10000000000 9216910780647 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6223784877/10000000000 : ℝ), (-128931971/400000000 : ℝ), (2481635253/10000000000 : ℝ)] ![(14062403565603/25000000000000 : ℝ), (25316564159127/100000000000000 : ℝ), (9216910780647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6223784877/10000000000 : ℝ)|^91 ≤ (14062403565603/25000000000000 : ℝ)^75
        have hw : |(6223784877/10000000000 : ℝ)|=(6223784877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128931971/400000000 : ℝ)|^91 ≤ (25316564159127/100000000000000 : ℝ)^75
        have hw : |(-128931971/400000000 : ℝ)|=(128931971/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2481635253/10000000000 : ℝ)|^91 ≤ (9216910780647/50000000000000 : ℝ)^75
        have hw : |(2481635253/10000000000 : ℝ)|=(2481635253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327037 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
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
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-761903599/10000000000 : ℝ)*X 0 0+(-6713383583/10000000000 : ℝ)*X 0 1+(2051986651/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4913684311/10000000000 : ℝ)*X 1 0+(378003111/1250000000 : ℝ)*X 1 1+(2072205447/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1616040067/2000000000 : ℝ)*X 0 0+(-1264809069/10000000000 : ℝ)*X 0 1+(2053932371/10000000000 : ℝ)*X 0 2+(1616040067/2000000000 : ℝ)*X 1 0+(-1264809069/10000000000 : ℝ)*X 1 1+(2053932371/10000000000 : ℝ)*X 1 2+(1616040067/2000000000 : ℝ)*X 2 0+(-1264809069/10000000000 : ℝ)*X 2 1+(2053932371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-393287507/5000000000 : ℝ)*X 0 0+(-1378950003/2000000000 : ℝ)*X 0 1+(3883385079/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4859544111/10000000000 : ℝ)*X 1 0+(3054033451/10000000000 : ℝ)*X 1 1+(2086190327/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4859543921/10000000000 : ℝ)*X 2 0+(-1466074411/5000000000 : ℝ)*X 2 1+(-4285600333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((815885477/1000000000 : ℝ)*X 0 0+(-137638539/2000000000 : ℝ)*X 0 1+(1216094677/5000000000 : ℝ)*X 0 2+(815885477/1000000000 : ℝ)*X 1 0+(-137638539/2000000000 : ℝ)*X 1 1+(1216094677/5000000000 : ℝ)*X 1 2+(815885477/1000000000 : ℝ)*X 2 0+(-137638539/2000000000 : ℝ)*X 2 1+(1216094677/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-50708953/1000000000 : ℝ)*X 0 0+(-6661749737/10000000000 : ℝ)*X 0 1+(216543253/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((240477437/500000000 : ℝ)*X 1 0+(3060886637/10000000000 : ℝ)*X 1 1+(421750669/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((103420183/200000000 : ℝ)*X 2 0+(-2850064593/10000000000 : ℝ)*X 2 1+(-1009358791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1684763009/2000000000 : ℝ)*X 0 0+(-299533973/2500000000 : ℝ)*X 0 1+(821051881/5000000000 : ℝ)*X 0 2+(1684763009/2000000000 : ℝ)*X 1 0+(-299533973/2500000000 : ℝ)*X 1 1+(821051881/5000000000 : ℝ)*X 1 2+(1684763009/2000000000 : ℝ)*X 2 0+(-299533973/2500000000 : ℝ)*X 2 1+(821051881/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-286940209/5000000000 : ℝ)*X 0 0+(-6871555689/10000000000 : ℝ)*X 0 1+(162214531/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2552109101/5000000000 : ℝ)*X 1 0+(742262709/2500000000 : ℝ)*X 1 1+(1998376331/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((958806533/2000000000 : ℝ)*X 2 0+(-3017131789/10000000000 : ℝ)*X 2 1+(-427417757/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((423698403/500000000 : ℝ)*X 0 0+(-763162289/10000000000 : ℝ)*X 0 1+(1954071327/10000000000 : ℝ)*X 0 2+(423698403/500000000 : ℝ)*X 1 0+(-763162289/10000000000 : ℝ)*X 1 1+(1954071327/10000000000 : ℝ)*X 1 2+(423698403/500000000 : ℝ)*X 2 0+(-763162289/10000000000 : ℝ)*X 2 1+(1954071327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2283/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2283/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (159421591054664967/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (103537/200000000000 : ℝ)*(base3) + (623249454707/100000000000 : ℝ)*(base40) + (3855522463467/1000000000000 : ℝ)*(base49) + (18693260313071/1000000000000 : ℝ)*(major_s0_0) + (18693260313071/1000000000000 : ℝ)*(major_s0_1) + (18693260313071/1000000000000 : ℝ)*(major_s0_2) + (1073195147/500000000000 : ℝ)*(sp_s0_1) + (64633729/1000000000000 : ℝ)*(sp_s0_6) + (28552730531013/1000000000000 : ℝ)*(sp_s0_7) + (7136745081603/250000000000 : ℝ)*(sp_s0_8) + (28551874904293/1000000000000 : ℝ)*(sp_s0_9) + (1104214953707/125000000000 : ℝ)*(sp_s0_13) + (450541499/125000000000 : ℝ)*(sp_s0_15) + (5347667/6250000000 : ℝ)*(sp_s0_23) + (883378478107/100000000000 : ℝ)*(f.failure) + (28552730531013/1000000000000 : ℝ)*(f.sum) + (46403639329627/1250000000000000000000000000 : ℝ)*base62 + (495010920899363/5000000000000000000000000000 : ℝ)*base64 + (87416516100637/5000000000000000000000000000 : ℝ)*base67 + (738431109545373/2500000000000000000000000000 : ℝ)*base69 + (1005218597191383/5000000000000000000000000000 : ℝ)*base71 + (1447420905399363/5000000000000000000000000000 : ℝ)*base73 + (147522507795373/2500000000000000000000000000 : ℝ)*base75 + (122860958454627/2500000000000000000000000000 : ℝ)*base76 + (528411857/5000000000000000000000 : ℝ)*base78 + (9623/10000000000000000 : ℝ)*base86 + (9623/10000000000000000 : ℝ)*base88 + (9623/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10407/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-10407/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15158700838594812782517/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4011681/1000000000000 : ℝ)*(base39) + (823791861453/125000000000 : ℝ)*(base40) + (396753247569/125000000000 : ℝ)*(base49) + (18112637124449/1000000000000 : ℝ)*(major_s0_0) + (18112637124449/1000000000000 : ℝ)*(major_s0_1) + (18112637124449/1000000000000 : ℝ)*(major_s0_2) + (54034379/500000000000 : ℝ)*(sp_s0_0) + (222596891/200000000000 : ℝ)*(sp_s0_1) + (56156903/200000000000 : ℝ)*(sp_s0_6) + (27665759684979/1000000000000 : ℝ)*(sp_s0_14) + (13832377384641/500000000000 : ℝ)*(sp_s0_15) + (13832933876869/500000000000 : ℝ)*(sp_s0_16) + (8559005940851/1000000000000 : ℝ)*(sp_s0_20) + (115727459/1000000000000 : ℝ)*(sp_s0_27) + (342376098113/40000000000 : ℝ)*(f.failure) + (13832933876869/500000000000 : ℝ)*(f.sum) + (618238655496387/1250000000000000000000000000 : ℝ)*base63 + (4525874371981197/5000000000000000000000000000 : ℝ)*base64 + (3605474632518803/5000000000000000000000000000 : ℝ)*base67 + (2949752950246387/2500000000000000000000000000 : ℝ)*base69 + (3157313745511577/5000000000000000000000000000 : ℝ)*base71 + (2522249744481197/5000000000000000000000000000 : ℝ)*base73 + (1702124821496387/2500000000000000000000000000 : ℝ)*base75 + (457640064496387/2500000000000000000000000000 : ℝ)*base77 + (73860397/2500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (5957/4000000000000000 : ℝ)*base86 + (5957/4000000000000000 : ℝ)*base88 + (5957/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13137/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13137/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (48954894915133581/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (7817437609779/1000000000000 : ℝ)*(base40) + (40129581561/10000000000 : ℝ)*(base49) + (77677/500000000000 : ℝ)*(base59) + (21106479688271/1000000000000 : ℝ)*(major_s0_0) + (21106479688271/1000000000000 : ℝ)*(major_s0_1) + (21106479688271/1000000000000 : ℝ)*(major_s0_2) + (3576087/125000000000 : ℝ)*(sp_s0_0) + (1406671/1000000000000 : ℝ)*(sp_s0_6) + (6560723/125000000000 : ℝ)*(sp_s0_7) + (2619151/100000000000 : ℝ)*(sp_s0_20) + (4029836038771/125000000000 : ℝ)*(sp_s0_21) + (4029846175581/125000000000 : ℝ)*(sp_s0_22) + (4029846175581/125000000000 : ℝ)*(sp_s0_23) + (9974160741873/1000000000000 : ℝ)*(sp_s0_27) + (9974188340053/1000000000000 : ℝ)*(f.failure) + (4029846175581/125000000000 : ℝ)*(f.sum) + (403892523662027/1250000000000000000000000000 : ℝ)*base62 + (3704867799704963/5000000000000000000000000000 : ℝ)*base64 + (94688122295037/5000000000000000000000000000 : ℝ)*base67 + (485298349962973/2500000000000000000000000000 : ℝ)*base69 + (1287691901720983/5000000000000000000000000000 : ℝ)*base71 + (1022176693704963/5000000000000000000000000000 : ℝ)*base73 + (462842343962973/2500000000000000000000000000 : ℝ)*base75 + (398991450287027/2500000000000000000000000000 : ℝ)*base76 + (1068492209/1250000000000000000000 : ℝ)*base78 + (144617/100000000000000000 : ℝ)*base86 + (144617/100000000000000000 : ℝ)*base88 + (144617/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (2283/25000 : ℝ) ^ (89/16 : ℝ) ≤ (82626211198429/50000000000000000000 : ℝ) := by
    have hpowers : (2283/25000 : ℝ)^89 ≤ (82626211198429/50000000000000000000 : ℝ)^16 := by
      have hnat : (2283 : ℕ)^89*50000000000000000000^16 ≤ 82626211198429^16*25000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2283 25000 82626211198429 50000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2283/25000 : ℝ)) (X := (82626211198429/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50000082626211198429/50000000000000000000 : ℝ) ≤ (10000002970828053/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (50000082626211198429/50000000000000000000 : ℝ)^16 ≤ (10000002970828053/10000000000000000 : ℝ)^89 := by
      have hnat : (50000082626211198429 : ℕ)^16*10000000000000000^89 ≤ 10000002970828053^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000082626211198429 50000000000000000000 10000002970828053 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002970828053/10000000000000000 : ℝ)) (X := (50000082626211198429/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25000082626211198429/25000000000000000000 : ℝ) ≤ (5000002970826039/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (25000082626211198429/25000000000000000000 : ℝ)^16 ≤ (5000002970826039/5000000000000000 : ℝ)^89 := by
      have hnat : (25000082626211198429 : ℕ)^16*5000000000000000^89 ≤ 5000002970826039^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000082626211198429 25000000000000000000 5000002970826039 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000002970826039/5000000000000000 : ℝ)) (X := (25000082626211198429/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2970828053/913200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(39610987/12176000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (2283/25000 : ℝ)) (alpha := (2970828053/913200000000000 : ℝ)) (beta := (39610987/12176000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2283/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2970828053/913200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(39610987/12176000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (10407/50000 : ℝ) ^ (89/16 : ℝ) ≤ (807835162055547/5000000000000000000 : ℝ) := by
    have hpowers : (10407/50000 : ℝ)^89 ≤ (807835162055547/5000000000000000000 : ℝ)^16 := by
      have hnat : (10407 : ℕ)^89*5000000000000000000^16 ≤ 807835162055547^16*50000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10407 50000 807835162055547 5000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10407/50000 : ℝ)) (X := (807835162055547/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (5000807835162055547/5000000000000000000 : ℝ) ≤ (10000290438342339/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (5000807835162055547/5000000000000000000 : ℝ)^16 ≤ (10000290438342339/10000000000000000 : ℝ)^89 := by
      have hnat : (5000807835162055547 : ℕ)^16*10000000000000000^89 ≤ 10000290438342339^89*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000807835162055547 5000000000000000000 10000290438342339 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000290438342339/10000000000000000 : ℝ)) (X := (5000807835162055547/5000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (2500807835162055547/2500000000000000000 : ℝ) ≤ (5000290419102093/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2500807835162055547/2500000000000000000 : ℝ)^16 ≤ (5000290419102093/5000000000000000 : ℝ)^89 := by
      have hnat : (2500807835162055547 : ℕ)^16*5000000000000000^89 ≤ 5000290419102093^89*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500807835162055547 2500000000000000000 5000290419102093 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000290419102093/5000000000000000 : ℝ)) (X := (2500807835162055547/2500000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(290438342339/2081400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(96799953949/693800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (10407/50000 : ℝ)) (alpha := (290438342339/2081400000000000 : ℝ)) (beta := (96799953949/693800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (10407/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(290438342339/2081400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(96799953949/693800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13137/50000 : ℝ) ^ (89/16 : ℝ) ≤ (59035665439073651/100000000000000000000 : ℝ) := by
    have hpowers : (13137/50000 : ℝ)^89 ≤ (59035665439073651/100000000000000000000 : ℝ)^16 := by
      have hnat : (13137 : ℕ)^89*100000000000000000000^16 ≤ 59035665439073651^16*50000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13137 50000 59035665439073651 100000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13137/50000 : ℝ)) (X := (59035665439073651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100059035665439073651/100000000000000000000 : ℝ) ≤ (5000530529233983/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (100059035665439073651/100000000000000000000 : ℝ)^16 ≤ (5000530529233983/5000000000000000 : ℝ)^89 := by
      have hnat : (100059035665439073651 : ℕ)^16*5000000000000000^89 ≤ 5000530529233983^89*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100059035665439073651 100000000000000000000 5000530529233983 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000530529233983/5000000000000000 : ℝ)) (X := (100059035665439073651/100000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50059035665439073651/50000000000000000000 : ℝ) ≤ (5001060801786047/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (50059035665439073651/50000000000000000000 : ℝ)^16 ≤ (5001060801786047/5000000000000000 : ℝ)^89 := by
      have hnat : (50059035665439073651 : ℕ)^16*5000000000000000^89 ≤ 5001060801786047^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50059035665439073651 50000000000000000000 5001060801786047 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001060801786047/5000000000000000 : ℝ)) (X := (50059035665439073651/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(530529233983/1313700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(142853597/353906250000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (13137/50000 : ℝ)) (alpha := (530529233983/1313700000000000 : ℝ)) (beta := (142853597/353906250000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (13137/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(530529233983/1313700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(142853597/353906250000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-975879277/5000000000 : ℝ)*X 0 0+(-563833087/1000000000 : ℝ)*X 0 1+(108524523/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4695648273/10000000000 : ℝ)*X 1 0+(25956341/78125000 : ℝ)*X 1 1+(2043749167/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((938778219/2000000000 : ℝ)*X 2 0+(-415404897/1250000000 : ℝ)*X 2 1+(-511064553/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6223784877/10000000000 : ℝ)*X 0 0+(-128931971/400000000 : ℝ)*X 0 1+(2481635253/10000000000 : ℝ)*X 0 2+(6223784877/10000000000 : ℝ)*X 1 0+(-128931971/400000000 : ℝ)*X 1 1+(2481635253/10000000000 : ℝ)*X 1 2+(6223784877/10000000000 : ℝ)*X 2 0+(-128931971/400000000 : ℝ)*X 2 1+(2481635253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327037_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-484833/50000 : ℝ) < ((-211611/100000 : ℝ)*P 0+(-211611/100000 : ℝ)*P 1+(-211611/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-484833/50000 : ℝ) < (-344953504914279763599600453830423/36125504721875000000000000000000 : ℝ) := by norm_num
    linear_combination (17877/500000000000 : ℝ)*(base10) + (24057/500000000000 : ℝ)*(base19) + (26717/1000000000000 : ℝ)*(base24) + (169077230833/1000000000000 : ℝ)*(base39) + (92001694767/125000000000 : ℝ)*(base40) + (34559/1000000000000 : ℝ)*(base43) + (485952843279/1000000000000 : ℝ)*(base49) + (2943/500000000000 : ℝ)*(ratio_s0_1) + (211611/100000 : ℝ)*(major_s1_0) + (2116109965441/1000000000000 : ℝ)*(major_s1_1) + (211611/100000 : ℝ)*(major_s1_2) + (795729360621/250000000000 : ℝ)*(sp_s1_0) + (3182917464683/1000000000000 : ℝ)*(sp_s1_1) + (1591458725761/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (3182917512797/1000000000000 : ℝ)*(f.sum) + (2833029047233632719/9114450600000000000000000000000 : ℝ)*base62 + (19639588923/37750000000000000000000 : ℝ)*base64 + (17302520197091/693800000000000000000000000 : ℝ)*base67 + (3772259527961/43790000000000000000000000 : ℝ)*base68 + (23521406547189/71819375000000000000000000 : ℝ)*base70 + (4039586469579/3805000000000000000000000 : ℝ)*base73 + (1181046073136101/2081400000000000000000000000 : ℝ)*base74 + (92927695669/237812500000000000000000 : ℝ)*base76 + (754720946988639691/527981800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c327038_s0_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-42477007/625000000 : ℝ)*x 0 + (-893066139/2000000000 : ℝ)*x 1 + (-1286982567/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42477007/625000000 : ℝ)^91 ≤ (382964914213/10000000000000 : ℝ)^75 := by
    have hnat : (42477007 : ℕ)^91*10000000000000^75 ≤ 382964914213^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42477007 625000000 382964914213 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (893066139/2000000000 : ℝ)^91 ≤ (18798610047011/50000000000000 : ℝ)^75 := by
    have hnat : (893066139 : ℕ)^91*50000000000000^75 ≤ 18798610047011^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893066139 2000000000 18798610047011 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1286982567/2000000000 : ℝ)^91 ≤ (29286565371819/50000000000000 : ℝ)^75 := by
    have hnat : (1286982567 : ℕ)^91*50000000000000^75 ≤ 29286565371819^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286982567 2000000000 29286565371819 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42477007/625000000 : ℝ), (-893066139/2000000000 : ℝ), (-1286982567/2000000000 : ℝ)] ![(382964914213/10000000000000 : ℝ), (18798610047011/50000000000000 : ℝ), (29286565371819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42477007/625000000 : ℝ)|^91 ≤ (382964914213/10000000000000 : ℝ)^75
        have hw : |(-42477007/625000000 : ℝ)|=(42477007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-893066139/2000000000 : ℝ)|^91 ≤ (18798610047011/50000000000000 : ℝ)^75
        have hw : |(-893066139/2000000000 : ℝ)|=(893066139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1286982567/2000000000 : ℝ)|^91 ≤ (29286565371819/50000000000000 : ℝ)^75
        have hw : |(-1286982567/2000000000 : ℝ)|=(1286982567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327038_s0_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5000368967/10000000000 : ℝ)*x 0 + (4082206573/10000000000 : ℝ)*x 1 + (-748523437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5000368967/10000000000 : ℝ)^91 ≤ (10782740764457/25000000000000 : ℝ)^75 := by
    have hnat : (5000368967 : ℕ)^91*25000000000000^75 ≤ 10782740764457^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5000368967 10000000000 10782740764457 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4082206573/10000000000 : ℝ)^91 ≤ (16859935566813/50000000000000 : ℝ)^75 := by
    have hnat : (4082206573 : ℕ)^91*50000000000000^75 ≤ 16859935566813^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4082206573 10000000000 16859935566813 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748523437/2500000000 : ℝ)^91 ≤ (23149165786569/100000000000000 : ℝ)^75 := by
    have hnat : (748523437 : ℕ)^91*100000000000000^75 ≤ 23149165786569^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748523437 2500000000 23149165786569 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5000368967/10000000000 : ℝ), (4082206573/10000000000 : ℝ), (-748523437/2500000000 : ℝ)] ![(10782740764457/25000000000000 : ℝ), (16859935566813/50000000000000 : ℝ), (23149165786569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5000368967/10000000000 : ℝ)|^91 ≤ (10782740764457/25000000000000 : ℝ)^75
        have hw : |(5000368967/10000000000 : ℝ)|=(5000368967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4082206573/10000000000 : ℝ)|^91 ≤ (16859935566813/50000000000000 : ℝ)^75
        have hw : |(4082206573/10000000000 : ℝ)|=(4082206573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-748523437/2500000000 : ℝ)|^91 ≤ (23149165786569/100000000000000 : ℝ)^75
        have hw : |(-748523437/2500000000 : ℝ)|=(748523437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327038_s0_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2500184581/5000000000 : ℝ)*x 0 + (-4082206453/10000000000 : ℝ)*x 1 + (149704683/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2500184581/5000000000 : ℝ)^91 ≤ (21565482549317/50000000000000 : ℝ)^75 := by
    have hnat : (2500184581 : ℕ)^91*50000000000000^75 ≤ 21565482549317^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500184581 5000000000 21565482549317 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4082206453/10000000000 : ℝ)^91 ≤ (1685993496547/5000000000000 : ℝ)^75 := by
    have hnat : (4082206453 : ℕ)^91*5000000000000^75 ≤ 1685993496547^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4082206453 10000000000 1685993496547 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149704683/500000000 : ℝ)^91 ≤ (289364562013/1250000000000 : ℝ)^75 := by
    have hnat : (149704683 : ℕ)^91*1250000000000^75 ≤ 289364562013^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149704683 500000000 289364562013 1250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2500184581/5000000000 : ℝ), (-4082206453/10000000000 : ℝ), (149704683/500000000 : ℝ)] ![(21565482549317/50000000000000 : ℝ), (1685993496547/5000000000000 : ℝ), (289364562013/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2500184581/5000000000 : ℝ)|^91 ≤ (21565482549317/50000000000000 : ℝ)^75
        have hw : |(2500184581/5000000000 : ℝ)|=(2500184581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4082206453/10000000000 : ℝ)|^91 ≤ (1685993496547/5000000000000 : ℝ)^75
        have hw : |(-4082206453/10000000000 : ℝ)|=(4082206453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149704683/500000000 : ℝ)|^91 ≤ (289364562013/1250000000000 : ℝ)^75
        have hw : |(149704683/500000000 : ℝ)|=(149704683/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327038_s0_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7812455567/10000000000 : ℝ)*x 0 + (-302751861/2000000000 : ℝ)*x 1 + (-272681629/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7812455567/10000000000 : ℝ)^91 ≤ (74116614467441/100000000000000 : ℝ)^75 := by
    have hnat : (7812455567 : ℕ)^91*100000000000000^75 ≤ 74116614467441^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7812455567 10000000000 74116614467441 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302751861/2000000000 : ℝ)^91 ≤ (10118953850737/100000000000000 : ℝ)^75 := by
    have hnat : (302751861 : ℕ)^91*100000000000000^75 ≤ 10118953850737^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302751861 2000000000 10118953850737 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272681629/1250000000 : ℝ)^91 ≤ (15764431668117/100000000000000 : ℝ)^75 := by
    have hnat : (272681629 : ℕ)^91*100000000000000^75 ≤ 15764431668117^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272681629 1250000000 15764431668117 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7812455567/10000000000 : ℝ), (-302751861/2000000000 : ℝ), (-272681629/1250000000 : ℝ)] ![(74116614467441/100000000000000 : ℝ), (10118953850737/100000000000000 : ℝ), (15764431668117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7812455567/10000000000 : ℝ)|^91 ≤ (74116614467441/100000000000000 : ℝ)^75
        have hw : |(7812455567/10000000000 : ℝ)|=(7812455567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-302751861/2000000000 : ℝ)|^91 ≤ (10118953850737/100000000000000 : ℝ)^75
        have hw : |(-302751861/2000000000 : ℝ)|=(302751861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272681629/1250000000 : ℝ)|^91 ≤ (15764431668117/100000000000000 : ℝ)^75
        have hw : |(-272681629/1250000000 : ℝ)|=(272681629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327038 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]]) : False := by
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
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-42477007/625000000 : ℝ)*X 0 0+(-893066139/2000000000 : ℝ)*X 0 1+(-1286982567/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327038_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5000368967/10000000000 : ℝ)*X 1 0+(4082206573/10000000000 : ℝ)*X 1 1+(-748523437/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327038_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2500184581/5000000000 : ℝ)*X 2 0+(-4082206453/10000000000 : ℝ)*X 2 1+(149704683/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327038_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((7812455567/10000000000 : ℝ)*X 0 0+(-302751861/2000000000 : ℝ)*X 0 1+(-272681629/1250000000 : ℝ)*X 0 2+(7812455567/10000000000 : ℝ)*X 1 0+(-302751861/2000000000 : ℝ)*X 1 1+(-272681629/1250000000 : ℝ)*X 1 2+(7812455567/10000000000 : ℝ)*X 2 0+(-302751861/2000000000 : ℝ)*X 2 1+(-272681629/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327038_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-484833/50000 : ℝ) < ((-211611/100000 : ℝ)*P 0+(-211611/100000 : ℝ)*P 1+(-211611/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-484833/50000 : ℝ) < (-24233532171730904144086498143/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51569/500000000000 : ℝ)*(base18) + (711/3906250000 : ℝ)*(base22) + (1017/25000000000 : ℝ)*(base25) + (17409076873/15625000000 : ℝ)*(base39) + (182446676419/500000000000 : ℝ)*(base40) + (8777/1000000000000 : ℝ)*(base43) + (32481/1000000000000 : ℝ)*(base49) + (34068010197/100000000000 : ℝ)*(base59) + (211611/100000 : ℝ)*(major_s0_0) + (2116109991223/1000000000000 : ℝ)*(major_s0_1) + (211611/100000 : ℝ)*(major_s0_2) + (1615568807059/500000000000 : ℝ)*(sp_s0_0) + (3231137519757/1000000000000 : ℝ)*(sp_s0_1) + (1615568695711/500000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (646227524579/200000000000 : ℝ)*(f.sum) + (58413149048251/2500000000000000000000000000 : ℝ)*base62 + (357087167/1000000000000000000000 : ℝ)*base65 + (1634214223499381/5000000000000000000000000000 : ℝ)*base67 + (1331805299/10000000000000000000000 : ℝ)*base68 + (5377732619/10000000000000000000000 : ℝ)*base71 + (246231319/625000000000000000000 : ℝ)*base72 + (374121525951749/2500000000000000000000000000 : ℝ)*base75 + (1697810943/5000000000000000000000 : ℝ)*base77 + (962279528499381/5000000000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p027_b016 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=37 ∨ c=38 := by omega
  rcases hc with rfl|rfl
  · exact collision_c327037 p hpa (by linarith only [hpb]) X hX
  · exact collision_c327038 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b016 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
