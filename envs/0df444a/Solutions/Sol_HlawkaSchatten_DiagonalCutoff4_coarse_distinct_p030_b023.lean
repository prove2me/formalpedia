-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b023
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:32:41.163746+00:00
-- url     : https://prove2.me/submissions/51046675-cbc0-48f6-ac80-dbcaceee7f77

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
theorem collision_support_c330052_s0_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-600321557/10000000000 : ℝ)*x 0 + (836729803/2500000000 : ℝ)*x 1 + (-1850344643/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (600321557/10000000000 : ℝ)^6 ≤ (684054528281/20000000000000 : ℝ)^5 := by
    have hnat : (600321557 : ℕ)^6*20000000000000^5 ≤ 684054528281^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600321557 10000000000 684054528281 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (836729803/2500000000 : ℝ)^6 ≤ (26888976734399/100000000000000 : ℝ)^5 := by
    have hnat : (836729803 : ℕ)^6*100000000000000^5 ≤ 26888976734399^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836729803 2500000000 26888976734399 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1850344643/2500000000 : ℝ)^6 ≤ (69690750606641/100000000000000 : ℝ)^5 := by
    have hnat : (1850344643 : ℕ)^6*100000000000000^5 ≤ 69690750606641^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850344643 2500000000 69690750606641 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-600321557/10000000000 : ℝ), (836729803/2500000000 : ℝ), (-1850344643/2500000000 : ℝ)] ![(684054528281/20000000000000 : ℝ), (26888976734399/100000000000000 : ℝ), (69690750606641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-600321557/10000000000 : ℝ)|^6 ≤ (684054528281/20000000000000 : ℝ)^5
        have hw : |(-600321557/10000000000 : ℝ)|=(600321557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(836729803/2500000000 : ℝ)|^6 ≤ (26888976734399/100000000000000 : ℝ)^5
        have hw : |(836729803/2500000000 : ℝ)|=(836729803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1850344643/2500000000 : ℝ)|^6 ≤ (69690750606641/100000000000000 : ℝ)^5
        have hw : |(-1850344643/2500000000 : ℝ)|=(1850344643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (982950667/2000000000 : ℝ)*x 0 + (-33877441/156250000 : ℝ)*x 1 + (-4794661599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (982950667/2000000000 : ℝ)^6 ≤ (5329814380373/12500000000000 : ℝ)^5 := by
    have hnat : (982950667 : ℕ)^6*12500000000000^5 ≤ 5329814380373^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982950667 2000000000 5329814380373 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33877441/156250000 : ℝ)^6 ≤ (15970138623309/100000000000000 : ℝ)^5 := by
    have hnat : (33877441 : ℕ)^6*100000000000000^5 ≤ 15970138623309^5*156250000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33877441 156250000 15970138623309 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4794661599/10000000000 : ℝ)^6 ≤ (20695673160967/50000000000000 : ℝ)^5 := by
    have hnat : (4794661599 : ℕ)^6*50000000000000^5 ≤ 20695673160967^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794661599 10000000000 20695673160967 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(982950667/2000000000 : ℝ), (-33877441/156250000 : ℝ), (-4794661599/10000000000 : ℝ)] ![(5329814380373/12500000000000 : ℝ), (15970138623309/100000000000000 : ℝ), (20695673160967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(982950667/2000000000 : ℝ)|^6 ≤ (5329814380373/12500000000000 : ℝ)^5
        have hw : |(982950667/2000000000 : ℝ)|=(982950667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33877441/156250000 : ℝ)|^6 ≤ (15970138623309/100000000000000 : ℝ)^5
        have hw : |(-33877441/156250000 : ℝ)|=(33877441/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4794661599/10000000000 : ℝ)|^6 ≤ (20695673160967/50000000000000 : ℝ)^5
        have hw : |(-4794661599/10000000000 : ℝ)|=(4794661599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4914753389/10000000000 : ℝ)*x 0 + (6134001969/10000000000 : ℝ)*x 1 + (340763763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4914753389/10000000000 : ℝ)^6 ≤ (10659628901291/25000000000000 : ℝ)^5 := by
    have hnat : (4914753389 : ℕ)^6*25000000000000^5 ≤ 10659628901291^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4914753389 10000000000 10659628901291 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6134001969/10000000000 : ℝ)^6 ≤ (27813951792999/50000000000000 : ℝ)^5 := by
    have hnat : (6134001969 : ℕ)^6*50000000000000^5 ≤ 27813951792999^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6134001969 10000000000 27813951792999 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340763763/10000000000 : ℝ)^6 ≤ (1733580792631/100000000000000 : ℝ)^5 := by
    have hnat : (340763763 : ℕ)^6*100000000000000^5 ≤ 1733580792631^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340763763 10000000000 1733580792631 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4914753389/10000000000 : ℝ), (6134001969/10000000000 : ℝ), (340763763/10000000000 : ℝ)] ![(10659628901291/25000000000000 : ℝ), (27813951792999/50000000000000 : ℝ), (1733580792631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4914753389/10000000000 : ℝ)|^6 ≤ (10659628901291/25000000000000 : ℝ)^5
        have hw : |(4914753389/10000000000 : ℝ)|=(4914753389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6134001969/10000000000 : ℝ)|^6 ≤ (27813951792999/50000000000000 : ℝ)^5
        have hw : |(6134001969/10000000000 : ℝ)|=(6134001969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340763763/10000000000 : ℝ)|^6 ≤ (1733580792631/100000000000000 : ℝ)^5
        have hw : |(340763763/10000000000 : ℝ)|=(340763763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_7 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-343743093/2500000000 : ℝ)*x 0 + (173231563/1250000000 : ℝ)*x 1 + (-337031157/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343743093/2500000000 : ℝ)^6 ≤ (9245976091911/100000000000000 : ℝ)^5 := by
    have hnat : (343743093 : ℕ)^6*100000000000000^5 ≤ 9245976091911^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343743093 2500000000 9245976091911 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173231563/1250000000 : ℝ)^6 ≤ (9333841312419/100000000000000 : ℝ)^5 := by
    have hnat : (173231563 : ℕ)^6*100000000000000^5 ≤ 9333841312419^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173231563 1250000000 9333841312419 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337031157/400000000 : ℝ)^6 ≤ (81420182583359/100000000000000 : ℝ)^5 := by
    have hnat : (337031157 : ℕ)^6*100000000000000^5 ≤ 81420182583359^5*400000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337031157 400000000 81420182583359 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-343743093/2500000000 : ℝ), (173231563/1250000000 : ℝ), (-337031157/400000000 : ℝ)] ![(9245976091911/100000000000000 : ℝ), (9333841312419/100000000000000 : ℝ), (81420182583359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-343743093/2500000000 : ℝ)|^6 ≤ (9245976091911/100000000000000 : ℝ)^5
        have hw : |(-343743093/2500000000 : ℝ)|=(343743093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(173231563/1250000000 : ℝ)|^6 ≤ (9333841312419/100000000000000 : ℝ)^5
        have hw : |(173231563/1250000000 : ℝ)|=(173231563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-337031157/400000000 : ℝ)|^6 ≤ (81420182583359/100000000000000 : ℝ)^5
        have hw : |(-337031157/400000000 : ℝ)|=(337031157/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_8 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1595633101/5000000000 : ℝ)*x 0 + (-76464483/625000000 : ℝ)*x 1 + (-7123914933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1595633101/5000000000 : ℝ)^6 ≤ (12697717002431/50000000000000 : ℝ)^5 := by
    have hnat : (1595633101 : ℕ)^6*50000000000000^5 ≤ 12697717002431^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595633101 5000000000 12697717002431 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76464483/625000000 : ℝ)^6 ≤ (8037031804807/100000000000000 : ℝ)^5 := by
    have hnat : (76464483 : ℕ)^6*100000000000000^5 ≤ 8037031804807^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76464483 625000000 8037031804807 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7123914933/10000000000 : ℝ)^6 ≤ (32503678793/48828125000 : ℝ)^5 := by
    have hnat : (7123914933 : ℕ)^6*48828125000^5 ≤ 32503678793^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7123914933 10000000000 32503678793 48828125000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1595633101/5000000000 : ℝ), (-76464483/625000000 : ℝ), (-7123914933/10000000000 : ℝ)] ![(12697717002431/50000000000000 : ℝ), (8037031804807/100000000000000 : ℝ), (32503678793/48828125000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1595633101/5000000000 : ℝ)|^6 ≤ (12697717002431/50000000000000 : ℝ)^5
        have hw : |(1595633101/5000000000 : ℝ)|=(1595633101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-76464483/625000000 : ℝ)|^6 ≤ (8037031804807/100000000000000 : ℝ)^5
        have hw : |(-76464483/625000000 : ℝ)|=(76464483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7123914933/10000000000 : ℝ)|^6 ≤ (32503678793/48828125000 : ℝ)^5
        have hw : |(-7123914933/10000000000 : ℝ)|=(7123914933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_9 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1595633019/5000000000 : ℝ)*x 0 + (7770092927/10000000000 : ℝ)*x 1 + (82605929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1595633019/5000000000 : ℝ)^6 ≤ (25395432438769/100000000000000 : ℝ)^5 := by
    have hnat : (1595633019 : ℕ)^6*100000000000000^5 ≤ 25395432438769^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595633019 5000000000 25395432438769 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7770092927/10000000000 : ℝ)^6 ≤ (18469343733663/25000000000000 : ℝ)^5 := by
    have hnat : (7770092927 : ℕ)^6*25000000000000^5 ≤ 18469343733663^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7770092927 10000000000 18469343733663 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82605929/5000000000 : ℝ)^6 ≤ (727192612807/100000000000000 : ℝ)^5 := by
    have hnat : (82605929 : ℕ)^6*100000000000000^5 ≤ 727192612807^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82605929 5000000000 727192612807 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1595633019/5000000000 : ℝ), (7770092927/10000000000 : ℝ), (82605929/5000000000 : ℝ)] ![(25395432438769/100000000000000 : ℝ), (18469343733663/25000000000000 : ℝ), (727192612807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1595633019/5000000000 : ℝ)|^6 ≤ (25395432438769/100000000000000 : ℝ)^5
        have hw : |(1595633019/5000000000 : ℝ)|=(1595633019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7770092927/10000000000 : ℝ)|^6 ≤ (18469343733663/25000000000000 : ℝ)^5
        have hw : |(7770092927/10000000000 : ℝ)|=(7770092927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82605929/5000000000 : ℝ)|^6 ≤ (727192612807/100000000000000 : ℝ)^5
        have hw : |(82605929/5000000000 : ℝ)|=(82605929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_13 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (131576461/312500000 : ℝ)*x 0 + (6887170657/10000000000 : ℝ)*x 1 + (-76450427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131576461/312500000 : ℝ)^6 ≤ (17707767843977/50000000000000 : ℝ)^5 := by
    have hnat : (131576461 : ℕ)^6*50000000000000^5 ≤ 17707767843977^5*312500000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131576461 312500000 17707767843977 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6887170657/10000000000 : ℝ)^6 ≤ (3995112660371/6250000000000 : ℝ)^5 := by
    have hnat : (6887170657 : ℕ)^6*6250000000000^5 ≤ 3995112660371^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6887170657 10000000000 3995112660371 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76450427/5000000000 : ℝ)^6 ≤ (662661735103/100000000000000 : ℝ)^5 := by
    have hnat : (76450427 : ℕ)^6*100000000000000^5 ≤ 662661735103^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76450427 5000000000 662661735103 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131576461/312500000 : ℝ), (6887170657/10000000000 : ℝ), (-76450427/5000000000 : ℝ)] ![(17707767843977/50000000000000 : ℝ), (3995112660371/6250000000000 : ℝ), (662661735103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131576461/312500000 : ℝ)|^6 ≤ (17707767843977/50000000000000 : ℝ)^5
        have hw : |(131576461/312500000 : ℝ)|=(131576461/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6887170657/10000000000 : ℝ)|^6 ≤ (3995112660371/6250000000000 : ℝ)^5
        have hw : |(6887170657/10000000000 : ℝ)|=(6887170657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-76450427/5000000000 : ℝ)|^6 ≤ (662661735103/100000000000000 : ℝ)^5
        have hw : |(-76450427/5000000000 : ℝ)|=(76450427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_14 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-46593151/2000000000 : ℝ)*x 0 + (392493289/2000000000 : ℝ)*x 1 + (-8710416981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46593151/2000000000 : ℝ)^6 ≤ (109837465621/10000000000000 : ℝ)^5 := by
    have hnat : (46593151 : ℕ)^6*10000000000000^5 ≤ 109837465621^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46593151 2000000000 109837465621 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (392493289/2000000000 : ℝ)^6 ≤ (14169766304897/100000000000000 : ℝ)^5 := by
    have hnat : (392493289 : ℕ)^6*100000000000000^5 ≤ 14169766304897^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392493289 2000000000 14169766304897 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8710416981/10000000000 : ℝ)^6 ≤ (84731859033443/100000000000000 : ℝ)^5 := by
    have hnat : (8710416981 : ℕ)^6*100000000000000^5 ≤ 84731859033443^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8710416981 10000000000 84731859033443 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46593151/2000000000 : ℝ), (392493289/2000000000 : ℝ), (-8710416981/10000000000 : ℝ)] ![(109837465621/10000000000000 : ℝ), (14169766304897/100000000000000 : ℝ), (84731859033443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46593151/2000000000 : ℝ)|^6 ≤ (109837465621/10000000000000 : ℝ)^5
        have hw : |(-46593151/2000000000 : ℝ)|=(46593151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(392493289/2000000000 : ℝ)|^6 ≤ (14169766304897/100000000000000 : ℝ)^5
        have hw : |(392493289/2000000000 : ℝ)|=(392493289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8710416981/10000000000 : ℝ)|^6 ≤ (84731859033443/100000000000000 : ℝ)^5
        have hw : |(-8710416981/10000000000 : ℝ)|=(8710416981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_15 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1809920227/10000000000 : ℝ)*x 0 + (-2387346771/10000000000 : ℝ)*x 1 + (-735923537/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1809920227/10000000000 : ℝ)^6 ≤ (12858529936247/100000000000000 : ℝ)^5 := by
    have hnat : (1809920227 : ℕ)^6*100000000000000^5 ≤ 12858529936247^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809920227 10000000000 12858529936247 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2387346771/10000000000 : ℝ)^6 ≤ (4481657013953/25000000000000 : ℝ)^5 := by
    have hnat : (2387346771 : ℕ)^6*25000000000000^5 ≤ 4481657013953^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387346771 10000000000 4481657013953 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (735923537/1000000000 : ℝ)^6 ≤ (4325927624473/6250000000000 : ℝ)^5 := by
    have hnat : (735923537 : ℕ)^6*6250000000000^5 ≤ 4325927624473^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735923537 1000000000 4325927624473 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1809920227/10000000000 : ℝ), (-2387346771/10000000000 : ℝ), (-735923537/1000000000 : ℝ)] ![(12858529936247/100000000000000 : ℝ), (4481657013953/25000000000000 : ℝ), (4325927624473/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1809920227/10000000000 : ℝ)|^6 ≤ (12858529936247/100000000000000 : ℝ)^5
        have hw : |(1809920227/10000000000 : ℝ)|=(1809920227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2387346771/10000000000 : ℝ)|^6 ≤ (4481657013953/25000000000000 : ℝ)^5
        have hw : |(-2387346771/10000000000 : ℝ)|=(2387346771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-735923537/1000000000 : ℝ)|^6 ≤ (4325927624473/6250000000000 : ℝ)^5
        have hw : |(-735923537/1000000000 : ℝ)|=(735923537/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_16 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (3511919891/5000000000 : ℝ)*x 0 + (3996697589/10000000000 : ℝ)*x 1 + (66330769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3511919891/5000000000 : ℝ)^6 ≤ (65446965627101/100000000000000 : ℝ)^5 := by
    have hnat : (3511919891 : ℕ)^6*100000000000000^5 ≤ 65446965627101^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3511919891 5000000000 65446965627101 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3996697589/10000000000 : ℝ)^6 ≤ (415864222827/1250000000000 : ℝ)^5 := by
    have hnat : (3996697589 : ℕ)^6*1250000000000^5 ≤ 415864222827^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3996697589 10000000000 415864222827 1250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66330769/2500000000 : ℝ)^6 ≤ (256779307919/20000000000000 : ℝ)^5 := by
    have hnat : (66330769 : ℕ)^6*20000000000000^5 ≤ 256779307919^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66330769 2500000000 256779307919 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3511919891/5000000000 : ℝ), (3996697589/10000000000 : ℝ), (66330769/2500000000 : ℝ)] ![(65446965627101/100000000000000 : ℝ), (415864222827/1250000000000 : ℝ), (256779307919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3511919891/5000000000 : ℝ)|^6 ≤ (65446965627101/100000000000000 : ℝ)^5
        have hw : |(3511919891/5000000000 : ℝ)|=(3511919891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3996697589/10000000000 : ℝ)|^6 ≤ (415864222827/1250000000000 : ℝ)^5
        have hw : |(3996697589/10000000000 : ℝ)|=(3996697589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66330769/2500000000 : ℝ)|^6 ≤ (256779307919/20000000000000 : ℝ)^5
        have hw : |(66330769/2500000000 : ℝ)|=(66330769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_20 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (8190356809/10000000000 : ℝ)*x 0 + (2626286597/10000000000 : ℝ)*x 1 + (-251035633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8190356809/10000000000 : ℝ)^6 ≤ (19674485996907/25000000000000 : ℝ)^5 := by
    have hnat : (8190356809 : ℕ)^6*25000000000000^5 ≤ 19674485996907^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8190356809 10000000000 19674485996907 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626286597/10000000000 : ℝ)^6 ≤ (10050335164249/50000000000000 : ℝ)^5 := by
    have hnat : (2626286597 : ℕ)^6*50000000000000^5 ≤ 10050335164249^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626286597 10000000000 10050335164249 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251035633/10000000000 : ℝ)^6 ≤ (1201385665007/100000000000000 : ℝ)^5 := by
    have hnat : (251035633 : ℕ)^6*100000000000000^5 ≤ 1201385665007^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251035633 10000000000 1201385665007 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8190356809/10000000000 : ℝ), (2626286597/10000000000 : ℝ), (-251035633/10000000000 : ℝ)] ![(19674485996907/25000000000000 : ℝ), (10050335164249/50000000000000 : ℝ), (1201385665007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8190356809/10000000000 : ℝ)|^6 ≤ (19674485996907/25000000000000 : ℝ)^5
        have hw : |(8190356809/10000000000 : ℝ)|=(8190356809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626286597/10000000000 : ℝ)|^6 ≤ (10050335164249/50000000000000 : ℝ)^5
        have hw : |(2626286597/10000000000 : ℝ)|=(2626286597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251035633/10000000000 : ℝ)|^6 ≤ (1201385665007/100000000000000 : ℝ)^5
        have hw : |(-251035633/10000000000 : ℝ)|=(251035633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_21 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-6236019/5000000000 : ℝ)*x 0 + (566288931/1250000000 : ℝ)*x 1 + (-1330173537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6236019/5000000000 : ℝ)^6 ≤ (32743485717/100000000000000 : ℝ)^5 := by
    have hnat : (6236019 : ℕ)^6*100000000000000^5 ≤ 32743485717^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6236019 5000000000 32743485717 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566288931/1250000000 : ℝ)^6 ≤ (7733634933773/20000000000000 : ℝ)^5 := by
    have hnat : (566288931 : ℕ)^6*20000000000000^5 ≤ 7733634933773^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566288931 1250000000 7733634933773 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1330173537/2000000000 : ℝ)^6 ≤ (61299081829563/100000000000000 : ℝ)^5 := by
    have hnat : (1330173537 : ℕ)^6*100000000000000^5 ≤ 61299081829563^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330173537 2000000000 61299081829563 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6236019/5000000000 : ℝ), (566288931/1250000000 : ℝ), (-1330173537/2000000000 : ℝ)] ![(32743485717/100000000000000 : ℝ), (7733634933773/20000000000000 : ℝ), (61299081829563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6236019/5000000000 : ℝ)|^6 ≤ (32743485717/100000000000000 : ℝ)^5
        have hw : |(-6236019/5000000000 : ℝ)|=(6236019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566288931/1250000000 : ℝ)|^6 ≤ (7733634933773/20000000000000 : ℝ)^5
        have hw : |(566288931/1250000000 : ℝ)|=(566288931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1330173537/2000000000 : ℝ)|^6 ≤ (61299081829563/100000000000000 : ℝ)^5
        have hw : |(-1330173537/2000000000 : ℝ)|=(1330173537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_22 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (6598019873/10000000000 : ℝ)*x 0 + (-2080184089/10000000000 : ℝ)*x 1 + (-763470089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6598019873/10000000000 : ℝ)^6 ≤ (7589381007901/12500000000000 : ℝ)^5 := by
    have hnat : (6598019873 : ℕ)^6*12500000000000^5 ≤ 7589381007901^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6598019873 10000000000 7589381007901 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080184089/10000000000 : ℝ)^6 ≤ (15195749450699/100000000000000 : ℝ)^5 := by
    have hnat : (2080184089 : ℕ)^6*100000000000000^5 ≤ 15195749450699^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080184089 10000000000 15195749450699 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (763470089/2500000000 : ℝ)^6 ≤ (24089202480229/100000000000000 : ℝ)^5 := by
    have hnat : (763470089 : ℕ)^6*100000000000000^5 ≤ 24089202480229^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763470089 2500000000 24089202480229 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6598019873/10000000000 : ℝ), (-2080184089/10000000000 : ℝ), (-763470089/2500000000 : ℝ)] ![(7589381007901/12500000000000 : ℝ), (15195749450699/100000000000000 : ℝ), (24089202480229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6598019873/10000000000 : ℝ)|^6 ≤ (7589381007901/12500000000000 : ℝ)^5
        have hw : |(6598019873/10000000000 : ℝ)|=(6598019873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080184089/10000000000 : ℝ)|^6 ≤ (15195749450699/100000000000000 : ℝ)^5
        have hw : |(-2080184089/10000000000 : ℝ)|=(2080184089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-763470089/2500000000 : ℝ)|^6 ≤ (24089202480229/100000000000000 : ℝ)^5
        have hw : |(-763470089/2500000000 : ℝ)|=(763470089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_23 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1227322657/5000000000 : ℝ)*x 0 + (58675189/78125000 : ℝ)*x 1 + (1533629893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1227322657/5000000000 : ℝ)^6 ≤ (3706947986797/20000000000000 : ℝ)^5 := by
    have hnat : (1227322657 : ℕ)^6*20000000000000^5 ≤ 3706947986797^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227322657 5000000000 3706947986797 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58675189/78125000 : ℝ)^6 ≤ (70924675948927/100000000000000 : ℝ)^5 := by
    have hnat : (58675189 : ℕ)^6*100000000000000^5 ≤ 70924675948927^5*78125000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58675189 78125000 70924675948927 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1533629893/10000000000 : ℝ)^6 ≤ (10540584109331/100000000000000 : ℝ)^5 := by
    have hnat : (1533629893 : ℕ)^6*100000000000000^5 ≤ 10540584109331^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533629893 10000000000 10540584109331 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1227322657/5000000000 : ℝ), (58675189/78125000 : ℝ), (1533629893/10000000000 : ℝ)] ![(3706947986797/20000000000000 : ℝ), (70924675948927/100000000000000 : ℝ), (10540584109331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1227322657/5000000000 : ℝ)|^6 ≤ (3706947986797/20000000000000 : ℝ)^5
        have hw : |(1227322657/5000000000 : ℝ)|=(1227322657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(58675189/78125000 : ℝ)|^6 ≤ (70924675948927/100000000000000 : ℝ)^5
        have hw : |(58675189/78125000 : ℝ)|=(58675189/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1533629893/10000000000 : ℝ)|^6 ≤ (10540584109331/100000000000000 : ℝ)^5
        have hw : |(1533629893/10000000000 : ℝ)|=(1533629893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s0_27 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4522082067/5000000000 : ℝ)*x 0 + (1454081979/10000000000 : ℝ)*x 1 + (-148461893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4522082067/5000000000 : ℝ)^6 ≤ (88642525793813/100000000000000 : ℝ)^5 := by
    have hnat : (4522082067 : ℕ)^6*100000000000000^5 ≤ 88642525793813^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522082067 5000000000 88642525793813 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1454081979/10000000000 : ℝ)^6 ≤ (4943979654261/50000000000000 : ℝ)^5 := by
    have hnat : (1454081979 : ℕ)^6*50000000000000^5 ≤ 4943979654261^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1454081979 10000000000 4943979654261 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148461893/5000000000 : ℝ)^6 ≤ (146951487793/10000000000000 : ℝ)^5 := by
    have hnat : (148461893 : ℕ)^6*10000000000000^5 ≤ 146951487793^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148461893 5000000000 146951487793 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4522082067/5000000000 : ℝ), (1454081979/10000000000 : ℝ), (-148461893/5000000000 : ℝ)] ![(88642525793813/100000000000000 : ℝ), (4943979654261/50000000000000 : ℝ), (146951487793/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4522082067/5000000000 : ℝ)|^6 ≤ (88642525793813/100000000000000 : ℝ)^5
        have hw : |(4522082067/5000000000 : ℝ)|=(4522082067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1454081979/10000000000 : ℝ)|^6 ≤ (4943979654261/50000000000000 : ℝ)^5
        have hw : |(1454081979/10000000000 : ℝ)|=(1454081979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-148461893/5000000000 : ℝ)|^6 ≤ (146951487793/10000000000000 : ℝ)^5
        have hw : |(-148461893/5000000000 : ℝ)|=(148461893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s1_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-1849098553/10000000000 : ℝ)*x 0 + (3670136657/10000000000 : ℝ)*x 1 + (-6238987681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1849098553/10000000000 : ℝ)^6 ≤ (6596629230123/50000000000000 : ℝ)^5 := by
    have hnat : (1849098553 : ℕ)^6*50000000000000^5 ≤ 6596629230123^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849098553 10000000000 6596629230123 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3670136657/10000000000 : ℝ)^6 ≤ (15017190390829/50000000000000 : ℝ)^5 := by
    have hnat : (3670136657 : ℕ)^6*50000000000000^5 ≤ 15017190390829^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3670136657 10000000000 15017190390829 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6238987681/10000000000 : ℝ)^6 ≤ (56772360747017/100000000000000 : ℝ)^5 := by
    have hnat : (6238987681 : ℕ)^6*100000000000000^5 ≤ 56772360747017^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6238987681 10000000000 56772360747017 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1849098553/10000000000 : ℝ), (3670136657/10000000000 : ℝ), (-6238987681/10000000000 : ℝ)] ![(6596629230123/50000000000000 : ℝ), (15017190390829/50000000000000 : ℝ), (56772360747017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1849098553/10000000000 : ℝ)|^6 ≤ (6596629230123/50000000000000 : ℝ)^5
        have hw : |(-1849098553/10000000000 : ℝ)|=(1849098553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3670136657/10000000000 : ℝ)|^6 ≤ (15017190390829/50000000000000 : ℝ)^5
        have hw : |(3670136657/10000000000 : ℝ)|=(3670136657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6238987681/10000000000 : ℝ)|^6 ≤ (56772360747017/100000000000000 : ℝ)^5
        have hw : |(-6238987681/10000000000 : ℝ)|=(6238987681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s1_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2277253769/5000000000 : ℝ)*x 0 + (-547675237/2000000000 : ℝ)*x 1 + (-931011397/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2277253769/5000000000 : ℝ)^6 ≤ (38916135801643/100000000000000 : ℝ)^5 := by
    have hnat : (2277253769 : ℕ)^6*100000000000000^5 ≤ 38916135801643^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277253769 5000000000 38916135801643 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547675237/2000000000 : ℝ)^6 ≤ (10567243996861/50000000000000 : ℝ)^5 := by
    have hnat : (547675237 : ℕ)^6*50000000000000^5 ≤ 10567243996861^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547675237 2000000000 10567243996861 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931011397/2000000000 : ℝ)^6 ≤ (39949376184767/100000000000000 : ℝ)^5 := by
    have hnat : (931011397 : ℕ)^6*100000000000000^5 ≤ 39949376184767^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931011397 2000000000 39949376184767 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2277253769/5000000000 : ℝ), (-547675237/2000000000 : ℝ), (-931011397/2000000000 : ℝ)] ![(38916135801643/100000000000000 : ℝ), (10567243996861/50000000000000 : ℝ), (39949376184767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2277253769/5000000000 : ℝ)|^6 ≤ (38916135801643/100000000000000 : ℝ)^5
        have hw : |(2277253769/5000000000 : ℝ)|=(2277253769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-547675237/2000000000 : ℝ)|^6 ≤ (10567243996861/50000000000000 : ℝ)^5
        have hw : |(-547675237/2000000000 : ℝ)|=(547675237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-931011397/2000000000 : ℝ)|^6 ≤ (39949376184767/100000000000000 : ℝ)^5
        have hw : |(-931011397/2000000000 : ℝ)|=(931011397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s1_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4595546359/10000000000 : ℝ)*x 0 + (5485165237/10000000000 : ℝ)*x 1 + (1710881601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4595546359/10000000000 : ℝ)^6 ≤ (9834325769413/25000000000000 : ℝ)^5 := by
    have hnat : (4595546359 : ℕ)^6*25000000000000^5 ≤ 9834325769413^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595546359 10000000000 9834325769413 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5485165237/10000000000 : ℝ)^6 ≤ (24321909169793/50000000000000 : ℝ)^5 := by
    have hnat : (5485165237 : ℕ)^6*50000000000000^5 ≤ 24321909169793^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485165237 10000000000 24321909169793 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1710881601/10000000000 : ℝ)^6 ≤ (480755142419/4000000000000 : ℝ)^5 := by
    have hnat : (1710881601 : ℕ)^6*4000000000000^5 ≤ 480755142419^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1710881601 10000000000 480755142419 4000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4595546359/10000000000 : ℝ), (5485165237/10000000000 : ℝ), (1710881601/10000000000 : ℝ)] ![(9834325769413/25000000000000 : ℝ), (24321909169793/50000000000000 : ℝ), (480755142419/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4595546359/10000000000 : ℝ)|^6 ≤ (9834325769413/25000000000000 : ℝ)^5
        have hw : |(4595546359/10000000000 : ℝ)|=(4595546359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5485165237/10000000000 : ℝ)|^6 ≤ (24321909169793/50000000000000 : ℝ)^5
        have hw : |(5485165237/10000000000 : ℝ)|=(5485165237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1710881601/10000000000 : ℝ)|^6 ≤ (480755142419/4000000000000 : ℝ)^5
        have hw : |(1710881601/10000000000 : ℝ)|=(1710881601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330052_s1_6 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (6794119987/10000000000 : ℝ)*x 0 + (3642180361/10000000000 : ℝ)*x 1 + (-1136034941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6794119987/10000000000 : ℝ)^6 ≤ (15721712986171/25000000000000 : ℝ)^5 := by
    have hnat : (6794119987 : ℕ)^6*25000000000000^5 ≤ 15721712986171^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6794119987 10000000000 15721712986171 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3642180361/10000000000 : ℝ)^6 ≤ (7440013894537/25000000000000 : ℝ)^5 := by
    have hnat : (3642180361 : ℕ)^6*25000000000000^5 ≤ 7440013894537^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3642180361 10000000000 7440013894537 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136034941/10000000000 : ℝ)^6 ≤ (919136557591/12500000000000 : ℝ)^5 := by
    have hnat : (1136034941 : ℕ)^6*12500000000000^5 ≤ 919136557591^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136034941 10000000000 919136557591 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6794119987/10000000000 : ℝ), (3642180361/10000000000 : ℝ), (-1136034941/10000000000 : ℝ)] ![(15721712986171/25000000000000 : ℝ), (7440013894537/25000000000000 : ℝ), (919136557591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6794119987/10000000000 : ℝ)|^6 ≤ (15721712986171/25000000000000 : ℝ)^5
        have hw : |(6794119987/10000000000 : ℝ)|=(6794119987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3642180361/10000000000 : ℝ)|^6 ≤ (7440013894537/25000000000000 : ℝ)^5
        have hw : |(3642180361/10000000000 : ℝ)|=(3642180361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1136034941/10000000000 : ℝ)|^6 ≤ (919136557591/12500000000000 : ℝ)^5
        have hw : |(-1136034941/10000000000 : ℝ)|=(1136034941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c330052 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (41553/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (41553/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (31839/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-600321557/10000000000 : ℝ)*X 0 0+(836729803/2500000000 : ℝ)*X 0 1+(-1850344643/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((982950667/2000000000 : ℝ)*X 1 0+(-33877441/156250000 : ℝ)*X 1 1+(-4794661599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4914753389/10000000000 : ℝ)*X 2 0+(6134001969/10000000000 : ℝ)*X 2 1+(340763763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-343743093/2500000000 : ℝ)*X 0 0+(173231563/1250000000 : ℝ)*X 0 1+(-337031157/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1595633101/5000000000 : ℝ)*X 1 0+(-76464483/625000000 : ℝ)*X 1 1+(-7123914933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1595633019/5000000000 : ℝ)*X 2 0+(7770092927/10000000000 : ℝ)*X 2 1+(82605929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((131576461/312500000 : ℝ)*X 0 0+(6887170657/10000000000 : ℝ)*X 0 1+(-76450427/5000000000 : ℝ)*X 0 2+(131576461/312500000 : ℝ)*X 1 0+(6887170657/10000000000 : ℝ)*X 1 1+(-76450427/5000000000 : ℝ)*X 1 2+(131576461/312500000 : ℝ)*X 2 0+(6887170657/10000000000 : ℝ)*X 2 1+(-76450427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-46593151/2000000000 : ℝ)*X 0 0+(392493289/2000000000 : ℝ)*X 0 1+(-8710416981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1809920227/10000000000 : ℝ)*X 1 0+(-2387346771/10000000000 : ℝ)*X 1 1+(-735923537/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3511919891/5000000000 : ℝ)*X 2 0+(3996697589/10000000000 : ℝ)*X 2 1+(66330769/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((8190356809/10000000000 : ℝ)*X 0 0+(2626286597/10000000000 : ℝ)*X 0 1+(-251035633/10000000000 : ℝ)*X 0 2+(8190356809/10000000000 : ℝ)*X 1 0+(2626286597/10000000000 : ℝ)*X 1 1+(-251035633/10000000000 : ℝ)*X 1 2+(8190356809/10000000000 : ℝ)*X 2 0+(2626286597/10000000000 : ℝ)*X 2 1+(-251035633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-6236019/5000000000 : ℝ)*X 0 0+(566288931/1250000000 : ℝ)*X 0 1+(-1330173537/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6598019873/10000000000 : ℝ)*X 1 0+(-2080184089/10000000000 : ℝ)*X 1 1+(-763470089/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1227322657/5000000000 : ℝ)*X 2 0+(58675189/78125000 : ℝ)*X 2 1+(1533629893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4522082067/5000000000 : ℝ)*X 0 0+(1454081979/10000000000 : ℝ)*X 0 1+(-148461893/5000000000 : ℝ)*X 0 2+(4522082067/5000000000 : ℝ)*X 1 0+(1454081979/10000000000 : ℝ)*X 1 1+(-148461893/5000000000 : ℝ)*X 1 2+(4522082067/5000000000 : ℝ)*X 2 0+(1454081979/10000000000 : ℝ)*X 2 1+(-148461893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((54787/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54787/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (58134629628939813/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (1027283611723/1000000000000 : ℝ)*(base7) + (10181840669/1000000000000 : ℝ)*(base39) + (103184106033/1000000000000 : ℝ)*(base59) + (1829379807517/1000000000000 : ℝ)*(major_s0_0) + (1829379807517/1000000000000 : ℝ)*(major_s0_1) + (1829379807517/1000000000000 : ℝ)*(major_s0_2) + (7659511/1000000000000 : ℝ)*(sp_s0_0) + (1606271/1000000000000 : ℝ)*(sp_s0_1) + (144398729039/62500000000 : ℝ)*(sp_s0_7) + (1155198006853/500000000000 : ℝ)*(sp_s0_8) + (2310399898401/1000000000000 : ℝ)*(sp_s0_9) + (366102668393/200000000000 : ℝ)*(sp_s0_13) + (6287133/500000000000 : ℝ)*(sp_s0_14) + (284803/125000000000 : ℝ)*(sp_s0_15) + (803229730241/1000000000000 : ℝ)*(f.failure) + (2310399898401/1000000000000 : ℝ)*(f.sum) + (154760613485283/5000000000000000000000000000 : ℝ)*base62 + (3736755388710197/10000000000000000000000000000 : ℝ)*base65 + (5454778860289803/10000000000000000000000000000 : ℝ)*base66 + (2537751109014717/10000000000000000000000000000 : ℝ)*base69 + (423336701637543/5000000000000000000000000000 : ℝ)*base70 + (8499470574710197/10000000000000000000000000000 : ℝ)*base72 + (3699956516014717/10000000000000000000000000000 : ℝ)*base75 + (3177878702014717/10000000000000000000000000000 : ℝ)*base77 + (749475237/2500000000000000000000 : ℝ)*base78 + (121527/100000000000000000 : ℝ)*base86 + (121527/100000000000000000 : ℝ)*base88 + (121527/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11151/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11151/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1251772114947268715799/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (529176439489/500000000000 : ℝ)*(base7) + (6810173143/1000000000000 : ℝ)*(base39) + (184313/1000000000000 : ℝ)*(base49) + (1358897/1000000000000 : ℝ)*(base53) + (841031017/12500000000 : ℝ)*(base59) + (794260948203/500000000000 : ℝ)*(major_s0_0) + (794260948203/500000000000 : ℝ)*(major_s0_1) + (1588520537509/1000000000000 : ℝ)*(major_s0_2) + (26490347/1000000000000 : ℝ)*(sp_s0_8) + (1917948411913/1000000000000 : ℝ)*(sp_s0_14) + (383584384313/200000000000 : ℝ)*(sp_s0_15) + (191794977081/100000000000 : ℝ)*(sp_s0_16) + (877904513349/500000000000 : ℝ)*(sp_s0_20) + (19580989/1000000000000 : ℝ)*(sp_s0_27) + (697475728709/1000000000000 : ℝ)*(f.failure) + (191794977081/100000000000 : ℝ)*(f.sum) + (175760068559583/2000000000000000000000000000 : ℝ)*base63 + (5272743268408131/10000000000000000000000000000 : ℝ)*base64 + (1855562054094323/5000000000000000000000000000 : ℝ)*base67 + (2530047709411909/10000000000000000000000000000 : ℝ)*base69 + (47392574264177/80000000000000000000000000 : ℝ)*base70 + (2689077639094323/5000000000000000000000000000 : ℝ)*base72 + (692566329306997/5000000000000000000000000000 : ℝ)*base74 + (756837528806997/5000000000000000000000000000 : ℝ)*base76 + (207405657/2500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (60877/100000000000000000 : ℝ)*base87 + (60877/100000000000000000 : ℝ)*base89 + (60877/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-44087/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-44087/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (45783555817410426528513/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40405930667/50000000000 : ℝ)*(base7) + (1596333/1000000000000 : ℝ)*(base15) + (45063804051/100000000000 : ℝ)*(base39) + (128238510687/1000000000000 : ℝ)*(base49) + (174570780331/500000000000 : ℝ)*(base59) + (1820925797297/1000000000000 : ℝ)*(major_s0_0) + (1820925797297/1000000000000 : ℝ)*(major_s0_1) + (1820925797297/1000000000000 : ℝ)*(major_s0_2) + (1124163/250000000000 : ℝ)*(sp_s0_2) + (53758487/1000000000000 : ℝ)*(sp_s0_9) + (2413502590407/1000000000000 : ℝ)*(sp_s0_21) + (1206750497037/500000000000 : ℝ)*(sp_s0_22) + (2413444335267/1000000000000 : ℝ)*(sp_s0_23) + (401909105779/250000000000 : ℝ)*(sp_s0_27) + (31980712391/40000000000 : ℝ)*(f.failure) + (2413502590407/1000000000000 : ℝ)*(f.sum) + (2069832974147503/5000000000000000000000000000 : ℝ)*base62 + (5855003654028823/10000000000000000000000000000 : ℝ)*base64 + (4434637216971177/10000000000000000000000000000 : ℝ)*base67 + (6792196081147503/10000000000000000000000000000 : ℝ)*base68 + (1229538833588163/5000000000000000000000000000 : ℝ)*base70 + (2534945274028823/10000000000000000000000000000 : ℝ)*base73 + (3744970451147503/10000000000000000000000000000 : ℝ)*base74 + (3033722999852497/10000000000000000000000000000 : ℝ)*base77 + (538340423/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (577/4000000000000000 : ℝ)*base86 + (577/4000000000000000 : ℝ)*base88 + (577/4000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (54787/100000 : ℝ) ^ (95/16 : ℝ) ≤ (2808004349604691069/100000000000000000000 : ℝ) := by
    have hpowers : (54787/100000 : ℝ)^95 ≤ (2808004349604691069/100000000000000000000 : ℝ)^16 := by
      have hnat : (54787 : ℕ)^95*100000000000000000000^16 ≤ 2808004349604691069^16*100000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54787 100000 2808004349604691069 100000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (54787/100000 : ℝ)) (X := (2808004349604691069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (102808004349604691069/100000000000000000000 : ℝ) ≤ (2009349965209549/2000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (102808004349604691069/100000000000000000000 : ℝ)^16 ≤ (2009349965209549/2000000000000000 : ℝ)^95 := by
      have hnat : (102808004349604691069 : ℕ)^16*2000000000000000^95 ≤ 2009349965209549^95*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102808004349604691069 100000000000000000000 2009349965209549 2000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2009349965209549/2000000000000000 : ℝ)) (X := (102808004349604691069/100000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (52808004349604691069/50000000000000000000 : ℝ) ≤ (10092449608789477/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (52808004349604691069/50000000000000000000 : ℝ)^16 ≤ (10092449608789477/10000000000000000 : ℝ)^95 := by
      have hnat : (52808004349604691069 : ℕ)^16*10000000000000000^95 ≤ 10092449608789477^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52808004349604691069 50000000000000000000 10092449608789477 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10092449608789477/10000000000000000 : ℝ)) (X := (52808004349604691069/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(9349965209549/1095740000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(11424945685433/1369675000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (54787/100000 : ℝ)) (alpha := (9349965209549/1095740000000000 : ℝ)) (beta := (11424945685433/1369675000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (54787/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(9349965209549/1095740000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(11424945685433/1369675000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (11151/20000 : ℝ) ^ (95/16 : ℝ) ≤ (1557866313605034557/50000000000000000000 : ℝ) := by
    have hpowers : (11151/20000 : ℝ)^95 ≤ (1557866313605034557/50000000000000000000 : ℝ)^16 := by
      have hnat : (11151 : ℕ)^95*50000000000000000000^16 ≤ 1557866313605034557^16*20000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11151 20000 1557866313605034557 50000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11151/20000 : ℝ)) (X := (1557866313605034557/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (51557866313605034557/50000000000000000000 : ℝ) ≤ (2010361667155183/2000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (51557866313605034557/50000000000000000000 : ℝ)^16 ≤ (2010361667155183/2000000000000000 : ℝ)^95 := by
      have hnat : (51557866313605034557 : ℕ)^16*2000000000000000^95 ≤ 2010361667155183^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51557866313605034557 50000000000000000000 2010361667155183 2000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2010361667155183/2000000000000000 : ℝ)) (X := (51557866313605034557/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (26557866313605034557/25000000000000000000 : ℝ) ≤ (404093233373213/400000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (26557866313605034557/25000000000000000000 : ℝ)^16 ≤ (404093233373213/400000000000000 : ℝ)^95 := by
      have hnat : (26557866313605034557 : ℕ)^16*400000000000000^95 ≤ 404093233373213^95*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26557866313605034557 25000000000000000000 404093233373213 400000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (404093233373213/400000000000000 : ℝ)) (X := (26557866313605034557/25000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(10361667155183/1115100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(561361095049/61950000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (11151/20000 : ℝ)) (alpha := (10361667155183/1115100000000000 : ℝ)) (beta := (561361095049/61950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (11151/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(10361667155183/1115100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(561361095049/61950000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (44087/100000 : ℝ) ^ (95/16 : ℝ) ≤ (772847621098251549/100000000000000000000 : ℝ) := by
    have hpowers : (44087/100000 : ℝ)^95 ≤ (772847621098251549/100000000000000000000 : ℝ)^16 := by
      have hnat : (44087 : ℕ)^95*100000000000000000000^16 ≤ 772847621098251549^16*100000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44087 100000 772847621098251549 100000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44087/100000 : ℝ)) (X := (772847621098251549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100772847621098251549/100000000000000000000 : ℝ) ≤ (200259495003707/200000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (100772847621098251549/100000000000000000000 : ℝ)^16 ≤ (200259495003707/200000000000000 : ℝ)^95 := by
      have hnat : (100772847621098251549 : ℕ)^16*200000000000000^95 ≤ 200259495003707^95*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100772847621098251549 100000000000000000000 200259495003707 200000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200259495003707/200000000000000 : ℝ)) (X := (100772847621098251549/100000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50772847621098251549/50000000000000000000 : ℝ) ≤ (10025867015421479/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (50772847621098251549/50000000000000000000 : ℝ)^16 ≤ (10025867015421479/10000000000000000 : ℝ)^95 := by
      have hnat : (50772847621098251549 : ℕ)^16*10000000000000000^95 ≤ 10025867015421479^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50772847621098251549 50000000000000000000 10025867015421479 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025867015421479/10000000000000000 : ℝ)) (X := (50772847621098251549/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(259495003707/88174000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(12892265236129/4408700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (44087/100000 : ℝ)) (alpha := (259495003707/88174000000000 : ℝ)) (beta := (12892265236129/4408700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (44087/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(259495003707/88174000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(12892265236129/4408700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1849098553/10000000000 : ℝ)*X 0 0+(3670136657/10000000000 : ℝ)*X 0 1+(-6238987681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2277253769/5000000000 : ℝ)*X 1 0+(-547675237/2000000000 : ℝ)*X 1 1+(-931011397/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4595546359/10000000000 : ℝ)*X 2 0+(5485165237/10000000000 : ℝ)*X 2 1+(1710881601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6794119987/10000000000 : ℝ)*X 0 0+(3642180361/10000000000 : ℝ)*X 0 1+(-1136034941/10000000000 : ℝ)*X 0 2+(6794119987/10000000000 : ℝ)*X 1 0+(3642180361/10000000000 : ℝ)*X 1 1+(-1136034941/10000000000 : ℝ)*X 1 2+(6794119987/10000000000 : ℝ)*X 2 0+(3642180361/10000000000 : ℝ)*X 2 1+(-1136034941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330052_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-533259/50000 : ℝ) < ((-227753/100000 : ℝ)*P 0+(-227753/100000 : ℝ)*P 1+(-227753/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-533259/50000 : ℝ) < (-474522701566190617916139103177608349/44890106206365000000000000000000000 : ℝ) := by norm_num
    linear_combination (211/500000000000 : ℝ)*(base12) + (147/125000000000 : ℝ)*(base25) + (504678598869/1000000000000 : ℝ)*(base39) + (13797734633/1000000000000 : ℝ)*(base49) + (613446942219/1000000000000 : ℝ)*(base59) + (4221/1000000000000 : ℝ)*(base60) + (227753/100000 : ℝ)*(major_s1_0) + (227753/100000 : ℝ)*(major_s1_1) + (227753/100000 : ℝ)*(major_s1_2) + (3523587853711/1000000000000 : ℝ)*(sp_s1_0) + (440448482923/125000000000 : ℝ)*(sp_s1_1) + (3523587853237/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (880896963533/250000000000 : ℝ)*(f.sum) + (6092865699752929/4916141370000000000000000000000 : ℝ)*base62 + (63538267407049/440870000000000000000000000 : ℝ)*base64 + (9053373262649/12390000000000000000000000 : ℝ)*base67 + (781332403469/27554375000000000000000000 : ℝ)*base68 + (14074620694140781/603848617250000000000000000000 : ℝ)*base70 + (126714961671564197/13696750000000000000000000 : ℝ)*base73 + (31365293234739533/111510000000000000000000000 : ℝ)*base74 + (17307015673003/547870000000000000000000000 : ℝ)*base76 + (39438109491906359/678810930000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (2313/250000000000 : ℝ)*base83 + (281/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p030_b023 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 52 ≤ c.val) (hhi : c.val < 53)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=52 := by omega
  rcases hc with rfl
  · exact collision_c330052 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 52 ≤ c.val) (hhi : c.val < 53)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b023 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
