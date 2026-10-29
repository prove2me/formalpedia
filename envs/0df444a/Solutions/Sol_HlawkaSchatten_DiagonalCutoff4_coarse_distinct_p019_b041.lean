-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019_b041
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:28:40.795039+00:00
-- url     : https://prove2.me/submissions/ab1b90d7-5503-4d2e-a996-c8e21fa2b7bf

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
theorem collision_support_c319081_s0_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138921027/5000000000 : ℝ)*x 0 + (2572211999/10000000000 : ℝ)*x 1 + (136851261/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138921027/5000000000 : ℝ)^5 ≤ (6919280353967/20000000000000 : ℝ)^4 := by
    have hnat : (2138921027 : ℕ)^5*20000000000000^4 ≤ 6919280353967^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138921027 5000000000 6919280353967 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2572211999/10000000000 : ℝ)^5 ≤ (4579556889931/25000000000000 : ℝ)^4 := by
    have hnat : (2572211999 : ℕ)^5*25000000000000^4 ≤ 4579556889931^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572211999 10000000000 4579556889931 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136851261/250000000 : ℝ)^5 ≤ (11771342664693/25000000000000 : ℝ)^4 := by
    have hnat : (136851261 : ℕ)^5*25000000000000^4 ≤ 11771342664693^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136851261 250000000 11771342664693 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138921027/5000000000 : ℝ), (2572211999/10000000000 : ℝ), (136851261/250000000 : ℝ)] ![(6919280353967/20000000000000 : ℝ), (4579556889931/25000000000000 : ℝ), (11771342664693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138921027/5000000000 : ℝ)|^5 ≤ (6919280353967/20000000000000 : ℝ)^4
        have hw : |(-2138921027/5000000000 : ℝ)|=(2138921027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2572211999/10000000000 : ℝ)|^5 ≤ (4579556889931/25000000000000 : ℝ)^4
        have hw : |(2572211999/10000000000 : ℝ)|=(2572211999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136851261/250000000 : ℝ)|^5 ≤ (11771342664693/25000000000000 : ℝ)^4
        have hw : |(136851261/250000000 : ℝ)|=(136851261/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3894091759/10000000000 : ℝ)*x 0 + (691833211/1000000000 : ℝ)*x 1 + (-1073188071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3894091759/10000000000 : ℝ)^5 ≤ (15380757694373/50000000000000 : ℝ)^4 := by
    have hnat : (3894091759 : ℕ)^5*50000000000000^4 ≤ 15380757694373^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3894091759 10000000000 15380757694373 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (691833211/1000000000 : ℝ)^5 ≤ (157739974551/250000000000 : ℝ)^4 := by
    have hnat : (691833211 : ℕ)^5*250000000000^4 ≤ 157739974551^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691833211 1000000000 157739974551 250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073188071/10000000000 : ℝ)^5 ≤ (6142494775941/100000000000000 : ℝ)^4 := by
    have hnat : (1073188071 : ℕ)^5*100000000000000^4 ≤ 6142494775941^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073188071 10000000000 6142494775941 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3894091759/10000000000 : ℝ), (691833211/1000000000 : ℝ), (-1073188071/10000000000 : ℝ)] ![(15380757694373/50000000000000 : ℝ), (157739974551/250000000000 : ℝ), (6142494775941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3894091759/10000000000 : ℝ)|^5 ≤ (15380757694373/50000000000000 : ℝ)^4
        have hw : |(3894091759/10000000000 : ℝ)|=(3894091759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(691833211/1000000000 : ℝ)|^5 ≤ (157739974551/250000000000 : ℝ)^4
        have hw : |(691833211/1000000000 : ℝ)|=(691833211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073188071/10000000000 : ℝ)|^5 ≤ (6142494775941/100000000000000 : ℝ)^4
        have hw : |(-1073188071/10000000000 : ℝ)|=(1073188071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2031620143/10000000000 : ℝ)*x 0 + (1804711309/5000000000 : ℝ)*x 1 + (6501787159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031620143/10000000000 : ℝ)^5 ≤ (2727929443257/20000000000000 : ℝ)^4 := by
    have hnat : (2031620143 : ℕ)^5*20000000000000^4 ≤ 2727929443257^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031620143 10000000000 2727929443257 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1804711309/5000000000 : ℝ)^5 ≤ (27976744029113/100000000000000 : ℝ)^4 := by
    have hnat : (1804711309 : ℕ)^5*100000000000000^4 ≤ 27976744029113^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804711309 5000000000 27976744029113 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6501787159/10000000000 : ℝ)^5 ≤ (3648975545807/6250000000000 : ℝ)^4 := by
    have hnat : (6501787159 : ℕ)^5*6250000000000^4 ≤ 3648975545807^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6501787159 10000000000 3648975545807 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2031620143/10000000000 : ℝ), (1804711309/5000000000 : ℝ), (6501787159/10000000000 : ℝ)] ![(2727929443257/20000000000000 : ℝ), (27976744029113/100000000000000 : ℝ), (3648975545807/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2031620143/10000000000 : ℝ)|^5 ≤ (2727929443257/20000000000000 : ℝ)^4
        have hw : |(2031620143/10000000000 : ℝ)|=(2031620143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1804711309/5000000000 : ℝ)|^5 ≤ (27976744029113/100000000000000 : ℝ)^4
        have hw : |(1804711309/5000000000 : ℝ)|=(1804711309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6501787159/10000000000 : ℝ)|^5 ≤ (3648975545807/6250000000000 : ℝ)^4
        have hw : |(6501787159/10000000000 : ℝ)|=(6501787159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106201609/2500000000 : ℝ)*x 0 + (245024377/1000000000 : ℝ)*x 1 + (5435626337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106201609/2500000000 : ℝ)^5 ≤ (36088418169319/100000000000000 : ℝ)^4 := by
    have hnat : (1106201609 : ℕ)^5*100000000000000^4 ≤ 36088418169319^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106201609 2500000000 36088418169319 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245024377/1000000000 : ℝ)^5 ≤ (215487275417/1250000000000 : ℝ)^4 := by
    have hnat : (245024377 : ℕ)^5*1250000000000^4 ≤ 215487275417^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245024377 1000000000 215487275417 1250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435626337/10000000000 : ℝ)^5 ≤ (11668149943921/25000000000000 : ℝ)^4 := by
    have hnat : (5435626337 : ℕ)^5*25000000000000^4 ≤ 11668149943921^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435626337 10000000000 11668149943921 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106201609/2500000000 : ℝ), (245024377/1000000000 : ℝ), (5435626337/10000000000 : ℝ)] ![(36088418169319/100000000000000 : ℝ), (215487275417/1250000000000 : ℝ), (11668149943921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106201609/2500000000 : ℝ)|^5 ≤ (36088418169319/100000000000000 : ℝ)^4
        have hw : |(-1106201609/2500000000 : ℝ)|=(1106201609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(245024377/1000000000 : ℝ)|^5 ≤ (215487275417/1250000000000 : ℝ)^4
        have hw : |(245024377/1000000000 : ℝ)|=(245024377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435626337/10000000000 : ℝ)|^5 ≤ (11668149943921/25000000000000 : ℝ)^4
        have hw : |(5435626337/10000000000 : ℝ)|=(5435626337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2364987791/5000000000 : ℝ)*x 0 + (-2619231681/10000000000 : ℝ)*x 1 + (4999188221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2364987791/5000000000 : ℝ)^5 ≤ (3922596382029/10000000000000 : ℝ)^4 := by
    have hnat : (2364987791 : ℕ)^5*10000000000000^4 ≤ 3922596382029^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364987791 5000000000 3922596382029 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619231681/10000000000 : ℝ)^5 ≤ (18737747999319/100000000000000 : ℝ)^4 := by
    have hnat : (2619231681 : ℕ)^5*100000000000000^4 ≤ 18737747999319^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619231681 10000000000 18737747999319 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4999188221/10000000000 : ℝ)^5 ≤ (42036288160223/100000000000000 : ℝ)^4 := by
    have hnat : (4999188221 : ℕ)^5*100000000000000^4 ≤ 42036288160223^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999188221 10000000000 42036288160223 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2364987791/5000000000 : ℝ), (-2619231681/10000000000 : ℝ), (4999188221/10000000000 : ℝ)] ![(3922596382029/10000000000000 : ℝ), (18737747999319/100000000000000 : ℝ), (42036288160223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2364987791/5000000000 : ℝ)|^5 ≤ (3922596382029/10000000000000 : ℝ)^4
        have hw : |(2364987791/5000000000 : ℝ)|=(2364987791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2619231681/10000000000 : ℝ)|^5 ≤ (18737747999319/100000000000000 : ℝ)^4
        have hw : |(-2619231681/10000000000 : ℝ)|=(2619231681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4999188221/10000000000 : ℝ)|^5 ≤ (42036288160223/100000000000000 : ℝ)^4
        have hw : |(4999188221/10000000000 : ℝ)|=(4999188221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3650360757/10000000000 : ℝ)*x 0 + (58239889/80000000 : ℝ)*x 1 + (-102360813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3650360757/10000000000 : ℝ)^5 ≤ (2837394572517/10000000000000 : ℝ)^4 := by
    have hnat : (3650360757 : ℕ)^5*10000000000000^4 ≤ 2837394572517^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3650360757 10000000000 2837394572517 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58239889/80000000 : ℝ)^5 ≤ (13449098834983/20000000000000 : ℝ)^4 := by
    have hnat : (58239889 : ℕ)^5*20000000000000^4 ≤ 13449098834983^4*80000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58239889 80000000 13449098834983 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102360813/1250000000 : ℝ)^5 ≤ (4380560088883/100000000000000 : ℝ)^4 := by
    have hnat : (102360813 : ℕ)^5*100000000000000^4 ≤ 4380560088883^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102360813 1250000000 4380560088883 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3650360757/10000000000 : ℝ), (58239889/80000000 : ℝ), (-102360813/1250000000 : ℝ)] ![(2837394572517/10000000000000 : ℝ), (13449098834983/20000000000000 : ℝ), (4380560088883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3650360757/10000000000 : ℝ)|^5 ≤ (2837394572517/10000000000000 : ℝ)^4
        have hw : |(3650360757/10000000000 : ℝ)|=(3650360757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(58239889/80000000 : ℝ)|^5 ≤ (13449098834983/20000000000000 : ℝ)^4
        have hw : |(58239889/80000000 : ℝ)|=(58239889/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-102360813/1250000000 : ℝ)|^5 ≤ (4380560088883/100000000000000 : ℝ)^4
        have hw : |(-102360813/1250000000 : ℝ)|=(102360813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_12 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1831219409/10000000000 : ℝ)*x 0 + (182601841/500000000 : ℝ)*x 1 + (6612649979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1831219409/10000000000 : ℝ)^5 ≤ (2395827105809/20000000000000 : ℝ)^4 := by
    have hnat : (1831219409 : ℕ)^5*20000000000000^4 ≤ 2395827105809^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831219409 10000000000 2395827105809 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182601841/500000000 : ℝ)^5 ≤ (7097557882453/25000000000000 : ℝ)^4 := by
    have hnat : (182601841 : ℕ)^5*25000000000000^4 ≤ 7097557882453^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182601841 500000000 7097557882453 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6612649979/10000000000 : ℝ)^5 ≤ (14907658231837/25000000000000 : ℝ)^4 := by
    have hnat : (6612649979 : ℕ)^5*25000000000000^4 ≤ 14907658231837^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6612649979 10000000000 14907658231837 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1831219409/10000000000 : ℝ), (182601841/500000000 : ℝ), (6612649979/10000000000 : ℝ)] ![(2395827105809/20000000000000 : ℝ), (7097557882453/25000000000000 : ℝ), (14907658231837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1831219409/10000000000 : ℝ)|^5 ≤ (2395827105809/20000000000000 : ℝ)^4
        have hw : |(1831219409/10000000000 : ℝ)|=(1831219409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(182601841/500000000 : ℝ)|^5 ≤ (7097557882453/25000000000000 : ℝ)^4
        have hw : |(182601841/500000000 : ℝ)|=(182601841/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6612649979/10000000000 : ℝ)|^5 ≤ (14907658231837/25000000000000 : ℝ)^4
        have hw : |(6612649979/10000000000 : ℝ)|=(6612649979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-408904681/1000000000 : ℝ)*x 0 + (584748943/2500000000 : ℝ)*x 1 + (5838435393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408904681/1000000000 : ℝ)^5 ≤ (6539696572111/20000000000000 : ℝ)^4 := by
    have hnat : (408904681 : ℕ)^5*20000000000000^4 ≤ 6539696572111^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408904681 1000000000 6539696572111 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (584748943/2500000000 : ℝ)^5 ≤ (8133112886733/50000000000000 : ℝ)^4 := by
    have hnat : (584748943 : ℕ)^5*50000000000000^4 ≤ 8133112886733^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584748943 2500000000 8133112886733 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5838435393/10000000000 : ℝ)^5 ≤ (25517645676627/50000000000000 : ℝ)^4 := by
    have hnat : (5838435393 : ℕ)^5*50000000000000^4 ≤ 25517645676627^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5838435393 10000000000 25517645676627 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408904681/1000000000 : ℝ), (584748943/2500000000 : ℝ), (5838435393/10000000000 : ℝ)] ![(6539696572111/20000000000000 : ℝ), (8133112886733/50000000000000 : ℝ), (25517645676627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408904681/1000000000 : ℝ)|^5 ≤ (6539696572111/20000000000000 : ℝ)^4
        have hw : |(-408904681/1000000000 : ℝ)|=(408904681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(584748943/2500000000 : ℝ)|^5 ≤ (8133112886733/50000000000000 : ℝ)^4
        have hw : |(584748943/2500000000 : ℝ)|=(584748943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5838435393/10000000000 : ℝ)|^5 ≤ (25517645676627/50000000000000 : ℝ)^4
        have hw : |(5838435393/10000000000 : ℝ)|=(5838435393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5019080291/10000000000 : ℝ)*x 0 + (-2870988797/10000000000 : ℝ)*x 1 + (4488510863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5019080291/10000000000 : ℝ)^5 ≤ (82510689829/195312500000 : ℝ)^4 := by
    have hnat : (5019080291 : ℕ)^5*195312500000^4 ≤ 82510689829^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019080291 10000000000 82510689829 195312500000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2870988797/10000000000 : ℝ)^5 ≤ (10507741413077/50000000000000 : ℝ)^4 := by
    have hnat : (2870988797 : ℕ)^5*50000000000000^4 ≤ 10507741413077^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2870988797 10000000000 10507741413077 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488510863/10000000000 : ℝ)^5 ≤ (459238049531/1250000000000 : ℝ)^4 := by
    have hnat : (4488510863 : ℕ)^5*1250000000000^4 ≤ 459238049531^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488510863 10000000000 459238049531 1250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5019080291/10000000000 : ℝ), (-2870988797/10000000000 : ℝ), (4488510863/10000000000 : ℝ)] ![(82510689829/195312500000 : ℝ), (10507741413077/50000000000000 : ℝ), (459238049531/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5019080291/10000000000 : ℝ)|^5 ≤ (82510689829/195312500000 : ℝ)^4
        have hw : |(5019080291/10000000000 : ℝ)|=(5019080291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2870988797/10000000000 : ℝ)|^5 ≤ (10507741413077/50000000000000 : ℝ)^4
        have hw : |(-2870988797/10000000000 : ℝ)|=(2870988797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488510863/10000000000 : ℝ)|^5 ≤ (459238049531/1250000000000 : ℝ)^4
        have hw : |(4488510863/10000000000 : ℝ)|=(4488510863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3902066633/10000000000 : ℝ)*x 0 + (1409680633/2000000000 : ℝ)*x 1 + (-848198239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3902066633/10000000000 : ℝ)^5 ≤ (30840282785701/100000000000000 : ℝ)^4 := by
    have hnat : (3902066633 : ℕ)^5*100000000000000^4 ≤ 30840282785701^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3902066633 10000000000 30840282785701 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1409680633/2000000000 : ℝ)^5 ≤ (64582287244753/100000000000000 : ℝ)^4 := by
    have hnat : (1409680633 : ℕ)^5*100000000000000^4 ≤ 64582287244753^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1409680633 2000000000 64582287244753 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848198239/10000000000 : ℝ)^5 ≤ (1144357490679/25000000000000 : ℝ)^4 := by
    have hnat : (848198239 : ℕ)^5*25000000000000^4 ≤ 1144357490679^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848198239 10000000000 1144357490679 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3902066633/10000000000 : ℝ), (1409680633/2000000000 : ℝ), (-848198239/10000000000 : ℝ)] ![(30840282785701/100000000000000 : ℝ), (64582287244753/100000000000000 : ℝ), (1144357490679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3902066633/10000000000 : ℝ)|^5 ≤ (30840282785701/100000000000000 : ℝ)^4
        have hw : |(3902066633/10000000000 : ℝ)|=(3902066633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1409680633/2000000000 : ℝ)|^5 ≤ (64582287244753/100000000000000 : ℝ)^4
        have hw : |(1409680633/2000000000 : ℝ)|=(1409680633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-848198239/10000000000 : ℝ)|^5 ≤ (1144357490679/25000000000000 : ℝ)^4
        have hw : |(-848198239/10000000000 : ℝ)|=(848198239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_18 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (933408893/5000000000 : ℝ)*x 0 + (843020227/2500000000 : ℝ)*x 1 + (6824900497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933408893/5000000000 : ℝ)^5 ≤ (122709281287/1000000000000 : ℝ)^4 := by
    have hnat : (933408893 : ℕ)^5*1000000000000^4 ≤ 122709281287^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933408893 5000000000 122709281287 1000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (843020227/2500000000 : ℝ)^5 ≤ (3212051470727/12500000000000 : ℝ)^4 := by
    have hnat : (843020227 : ℕ)^5*12500000000000^4 ≤ 3212051470727^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843020227 2500000000 3212051470727 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6824900497/10000000000 : ℝ)^5 ≤ (62032660087899/100000000000000 : ℝ)^4 := by
    have hnat : (6824900497 : ℕ)^5*100000000000000^4 ≤ 62032660087899^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6824900497 10000000000 62032660087899 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(933408893/5000000000 : ℝ), (843020227/2500000000 : ℝ), (6824900497/10000000000 : ℝ)] ![(122709281287/1000000000000 : ℝ), (3212051470727/12500000000000 : ℝ), (62032660087899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(933408893/5000000000 : ℝ)|^5 ≤ (122709281287/1000000000000 : ℝ)^4
        have hw : |(933408893/5000000000 : ℝ)|=(933408893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(843020227/2500000000 : ℝ)|^5 ≤ (3212051470727/12500000000000 : ℝ)^4
        have hw : |(843020227/2500000000 : ℝ)|=(843020227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6824900497/10000000000 : ℝ)|^5 ≤ (62032660087899/100000000000000 : ℝ)^4
        have hw : |(6824900497/10000000000 : ℝ)|=(6824900497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_19 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-549261669/1250000000 : ℝ)*x 0 + (1252526883/5000000000 : ℝ)*x 1 + (1354933209/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549261669/1250000000 : ℝ)^5 ≤ (286204584429/800000000000 : ℝ)^4 := by
    have hnat : (549261669 : ℕ)^5*800000000000^4 ≤ 286204584429^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549261669 1250000000 286204584429 800000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252526883/5000000000 : ℝ)^5 ≤ (8861175107007/50000000000000 : ℝ)^4 := by
    have hnat : (1252526883 : ℕ)^5*50000000000000^4 ≤ 8861175107007^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252526883 5000000000 8861175107007 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354933209/2500000000 : ℝ)^5 ≤ (11625519179843/25000000000000 : ℝ)^4 := by
    have hnat : (1354933209 : ℕ)^5*25000000000000^4 ≤ 11625519179843^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354933209 2500000000 11625519179843 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549261669/1250000000 : ℝ), (1252526883/5000000000 : ℝ), (1354933209/2500000000 : ℝ)] ![(286204584429/800000000000 : ℝ), (8861175107007/50000000000000 : ℝ), (11625519179843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549261669/1250000000 : ℝ)|^5 ≤ (286204584429/800000000000 : ℝ)^4
        have hw : |(-549261669/1250000000 : ℝ)|=(549261669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1252526883/5000000000 : ℝ)|^5 ≤ (8861175107007/50000000000000 : ℝ)^4
        have hw : |(1252526883/5000000000 : ℝ)|=(1252526883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354933209/2500000000 : ℝ)|^5 ≤ (11625519179843/25000000000000 : ℝ)^4
        have hw : |(1354933209/2500000000 : ℝ)|=(1354933209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1137827827/2500000000 : ℝ)*x 0 + (-1525242821/5000000000 : ℝ)*x 1 + (2399692151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1137827827/2500000000 : ℝ)^5 ≤ (7476540208889/20000000000000 : ℝ)^4 := by
    have hnat : (1137827827 : ℕ)^5*20000000000000^4 ≤ 7476540208889^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137827827 2500000000 7476540208889 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1525242821/5000000000 : ℝ)^5 ≤ (4534101387099/20000000000000 : ℝ)^4 := by
    have hnat : (1525242821 : ℕ)^5*20000000000000^4 ≤ 4534101387099^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525242821 5000000000 4534101387099 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2399692151/5000000000 : ℝ)^5 ≤ (39946792008799/100000000000000 : ℝ)^4 := by
    have hnat : (2399692151 : ℕ)^5*100000000000000^4 ≤ 39946792008799^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399692151 5000000000 39946792008799 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1137827827/2500000000 : ℝ), (-1525242821/5000000000 : ℝ), (2399692151/5000000000 : ℝ)] ![(7476540208889/20000000000000 : ℝ), (4534101387099/20000000000000 : ℝ), (39946792008799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1137827827/2500000000 : ℝ)|^5 ≤ (7476540208889/20000000000000 : ℝ)^4
        have hw : |(1137827827/2500000000 : ℝ)|=(1137827827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1525242821/5000000000 : ℝ)|^5 ≤ (4534101387099/20000000000000 : ℝ)^4
        have hw : |(-1525242821/5000000000 : ℝ)|=(1525242821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2399692151/5000000000 : ℝ)|^5 ≤ (39946792008799/100000000000000 : ℝ)^4
        have hw : |(2399692151/5000000000 : ℝ)|=(2399692151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (81450491/200000000 : ℝ)*x 0 + (6803709299/10000000000 : ℝ)*x 1 + (-201454937/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81450491/200000000 : ℝ)^5 ≤ (8133353480741/25000000000000 : ℝ)^4 := by
    have hnat : (81450491 : ℕ)^5*25000000000000^4 ≤ 8133353480741^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81450491 200000000 8133353480741 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6803709299/10000000000 : ℝ)^5 ≤ (61791990685299/100000000000000 : ℝ)^4 := by
    have hnat : (6803709299 : ℕ)^5*100000000000000^4 ≤ 61791990685299^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6803709299 10000000000 61791990685299 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201454937/2000000000 : ℝ)^5 ≤ (5674595367159/100000000000000 : ℝ)^4 := by
    have hnat : (201454937 : ℕ)^5*100000000000000^4 ≤ 5674595367159^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201454937 2000000000 5674595367159 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81450491/200000000 : ℝ), (6803709299/10000000000 : ℝ), (-201454937/2000000000 : ℝ)] ![(8133353480741/25000000000000 : ℝ), (61791990685299/100000000000000 : ℝ), (5674595367159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81450491/200000000 : ℝ)|^5 ≤ (8133353480741/25000000000000 : ℝ)^4
        have hw : |(81450491/200000000 : ℝ)|=(81450491/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6803709299/10000000000 : ℝ)|^5 ≤ (61791990685299/100000000000000 : ℝ)^4
        have hw : |(6803709299/10000000000 : ℝ)|=(6803709299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201454937/2000000000 : ℝ)|^5 ≤ (5674595367159/100000000000000 : ℝ)^4
        have hw : |(-201454937/2000000000 : ℝ)|=(201454937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s0_25 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (922959053/5000000000 : ℝ)*x 0 + (3625593743/10000000000 : ℝ)*x 1 + (6624748743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (922959053/5000000000 : ℝ)^5 ≤ (1209944743381/10000000000000 : ℝ)^4 := by
    have hnat : (922959053 : ℕ)^5*10000000000000^4 ≤ 1209944743381^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922959053 5000000000 1209944743381 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3625593743/10000000000 : ℝ)^5 ≤ (28133510275541/100000000000000 : ℝ)^4 := by
    have hnat : (3625593743 : ℕ)^5*100000000000000^4 ≤ 28133510275541^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3625593743 10000000000 28133510275541 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6624748743/10000000000 : ℝ)^5 ≤ (5976704228717/10000000000000 : ℝ)^4 := by
    have hnat : (6624748743 : ℕ)^5*10000000000000^4 ≤ 5976704228717^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6624748743 10000000000 5976704228717 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(922959053/5000000000 : ℝ), (3625593743/10000000000 : ℝ), (6624748743/10000000000 : ℝ)] ![(1209944743381/10000000000000 : ℝ), (28133510275541/100000000000000 : ℝ), (5976704228717/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(922959053/5000000000 : ℝ)|^5 ≤ (1209944743381/10000000000000 : ℝ)^4
        have hw : |(922959053/5000000000 : ℝ)|=(922959053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3625593743/10000000000 : ℝ)|^5 ≤ (28133510275541/100000000000000 : ℝ)^4
        have hw : |(3625593743/10000000000 : ℝ)|=(3625593743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6624748743/10000000000 : ℝ)|^5 ≤ (5976704228717/10000000000000 : ℝ)^4
        have hw : |(6624748743/10000000000 : ℝ)|=(6624748743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-425429399/1000000000 : ℝ)*x 0 + (3286857331/10000000000 : ℝ)*x 1 + (195073649/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425429399/1000000000 : ℝ)^5 ≤ (17179257014729/50000000000000 : ℝ)^4 := by
    have hnat : (425429399 : ℕ)^5*50000000000000^4 ≤ 17179257014729^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425429399 1000000000 17179257014729 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3286857331/10000000000 : ℝ)^5 ≤ (4977440332629/20000000000000 : ℝ)^4 := by
    have hnat : (3286857331 : ℕ)^5*20000000000000^4 ≤ 4977440332629^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3286857331 10000000000 4977440332629 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195073649/400000000 : ℝ)^5 ≤ (40754284291567/100000000000000 : ℝ)^4 := by
    have hnat : (195073649 : ℕ)^5*100000000000000^4 ≤ 40754284291567^4*400000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195073649 400000000 40754284291567 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425429399/1000000000 : ℝ), (3286857331/10000000000 : ℝ), (195073649/400000000 : ℝ)] ![(17179257014729/50000000000000 : ℝ), (4977440332629/20000000000000 : ℝ), (40754284291567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425429399/1000000000 : ℝ)|^5 ≤ (17179257014729/50000000000000 : ℝ)^4
        have hw : |(-425429399/1000000000 : ℝ)|=(425429399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3286857331/10000000000 : ℝ)|^5 ≤ (4977440332629/20000000000000 : ℝ)^4
        have hw : |(3286857331/10000000000 : ℝ)|=(3286857331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(195073649/400000000 : ℝ)|^5 ≤ (40754284291567/100000000000000 : ℝ)^4
        have hw : |(195073649/400000000 : ℝ)|=(195073649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1103049493/2500000000 : ℝ)*x 0 + (-3408853569/10000000000 : ℝ)*x 1 + (184425973/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103049493/2500000000 : ℝ)^5 ≤ (8989980444057/25000000000000 : ℝ)^4 := by
    have hnat : (1103049493 : ℕ)^5*25000000000000^4 ≤ 8989980444057^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103049493 2500000000 8989980444057 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3408853569/10000000000 : ℝ)^5 ≤ (5209432656887/20000000000000 : ℝ)^4 := by
    have hnat : (3408853569 : ℕ)^5*20000000000000^4 ≤ 5209432656887^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3408853569 10000000000 5209432656887 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184425973/400000000 : ℝ)^5 ≤ (37992914920061/100000000000000 : ℝ)^4 := by
    have hnat : (184425973 : ℕ)^5*100000000000000^4 ≤ 37992914920061^4*400000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184425973 400000000 37992914920061 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103049493/2500000000 : ℝ), (-3408853569/10000000000 : ℝ), (184425973/400000000 : ℝ)] ![(8989980444057/25000000000000 : ℝ), (5209432656887/20000000000000 : ℝ), (37992914920061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103049493/2500000000 : ℝ)|^5 ≤ (8989980444057/25000000000000 : ℝ)^4
        have hw : |(1103049493/2500000000 : ℝ)|=(1103049493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3408853569/10000000000 : ℝ)|^5 ≤ (5209432656887/20000000000000 : ℝ)^4
        have hw : |(-3408853569/10000000000 : ℝ)|=(3408853569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184425973/400000000 : ℝ)|^5 ≤ (37992914920061/100000000000000 : ℝ)^4
        have hw : |(184425973/400000000 : ℝ)|=(184425973/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4180122983/10000000000 : ℝ)*x 0 + (1436832749/2500000000 : ℝ)*x 1 + (-587066177/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180122983/10000000000 : ℝ)^5 ≤ (16805689235099/50000000000000 : ℝ)^4 := by
    have hnat : (4180122983 : ℕ)^5*50000000000000^4 ≤ 16805689235099^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180122983 10000000000 16805689235099 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1436832749/2500000000 : ℝ)^5 ≤ (2001671257617/4000000000000 : ℝ)^4 := by
    have hnat : (1436832749 : ℕ)^5*4000000000000^4 ≤ 2001671257617^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1436832749 2500000000 2001671257617 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587066177/2500000000 : ℝ)^5 ≤ (16346840078933/100000000000000 : ℝ)^4 := by
    have hnat : (587066177 : ℕ)^5*100000000000000^4 ≤ 16346840078933^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587066177 2500000000 16346840078933 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180122983/10000000000 : ℝ), (1436832749/2500000000 : ℝ), (-587066177/2500000000 : ℝ)] ![(16805689235099/50000000000000 : ℝ), (2001671257617/4000000000000 : ℝ), (16346840078933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180122983/10000000000 : ℝ)|^5 ≤ (16805689235099/50000000000000 : ℝ)^4
        have hw : |(4180122983/10000000000 : ℝ)|=(4180122983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1436832749/2500000000 : ℝ)|^5 ≤ (2001671257617/4000000000000 : ℝ)^4
        have hw : |(1436832749/2500000000 : ℝ)|=(1436832749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-587066177/2500000000 : ℝ)|^5 ≤ (16346840078933/100000000000000 : ℝ)^4
        have hw : |(-587066177/2500000000 : ℝ)|=(587066177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319081_s1_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1431007963/5000000000 : ℝ)*x 0 + (3935040407/10000000000 : ℝ)*x 1 + (2774852107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1431007963/5000000000 : ℝ)^5 ≤ (10466706881123/50000000000000 : ℝ)^4 := by
    have hnat : (1431007963 : ℕ)^5*50000000000000^4 ≤ 10466706881123^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431007963 5000000000 10466706881123 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3935040407/10000000000 : ℝ)^5 ≤ (15583194800587/50000000000000 : ℝ)^4 := by
    have hnat : (3935040407 : ℕ)^5*50000000000000^4 ≤ 15583194800587^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3935040407 10000000000 15583194800587 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2774852107/5000000000 : ℝ)^5 ≤ (47900196619503/100000000000000 : ℝ)^4 := by
    have hnat : (2774852107 : ℕ)^5*100000000000000^4 ≤ 47900196619503^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774852107 5000000000 47900196619503 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1431007963/5000000000 : ℝ), (3935040407/10000000000 : ℝ), (2774852107/5000000000 : ℝ)] ![(10466706881123/50000000000000 : ℝ), (15583194800587/50000000000000 : ℝ), (47900196619503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1431007963/5000000000 : ℝ)|^5 ≤ (10466706881123/50000000000000 : ℝ)^4
        have hw : |(1431007963/5000000000 : ℝ)|=(1431007963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3935040407/10000000000 : ℝ)|^5 ≤ (15583194800587/50000000000000 : ℝ)^4
        have hw : |(3935040407/10000000000 : ℝ)|=(3935040407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2774852107/5000000000 : ℝ)|^5 ≤ (47900196619503/100000000000000 : ℝ)^4
        have hw : |(2774852107/5000000000 : ℝ)|=(2774852107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319081 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2138921027/5000000000 : ℝ)*X 0 0+(2572211999/10000000000 : ℝ)*X 0 1+(136851261/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3894091759/10000000000 : ℝ)*X 2 0+(691833211/1000000000 : ℝ)*X 2 1+(-1073188071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2031620143/10000000000 : ℝ)*X 0 0+(1804711309/5000000000 : ℝ)*X 0 1+(6501787159/10000000000 : ℝ)*X 0 2+(2031620143/10000000000 : ℝ)*X 1 0+(1804711309/5000000000 : ℝ)*X 1 1+(6501787159/10000000000 : ℝ)*X 1 2+(2031620143/10000000000 : ℝ)*X 2 0+(1804711309/5000000000 : ℝ)*X 2 1+(6501787159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1106201609/2500000000 : ℝ)*X 0 0+(245024377/1000000000 : ℝ)*X 0 1+(5435626337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2364987791/5000000000 : ℝ)*X 1 0+(-2619231681/10000000000 : ℝ)*X 1 1+(4999188221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3650360757/10000000000 : ℝ)*X 2 0+(58239889/80000000 : ℝ)*X 2 1+(-102360813/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((1831219409/10000000000 : ℝ)*X 0 0+(182601841/500000000 : ℝ)*X 0 1+(6612649979/10000000000 : ℝ)*X 0 2+(1831219409/10000000000 : ℝ)*X 1 0+(182601841/500000000 : ℝ)*X 1 1+(6612649979/10000000000 : ℝ)*X 1 2+(1831219409/10000000000 : ℝ)*X 2 0+(182601841/500000000 : ℝ)*X 2 1+(6612649979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-408904681/1000000000 : ℝ)*X 0 0+(584748943/2500000000 : ℝ)*X 0 1+(5838435393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((5019080291/10000000000 : ℝ)*X 1 0+(-2870988797/10000000000 : ℝ)*X 1 1+(4488510863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3902066633/10000000000 : ℝ)*X 2 0+(1409680633/2000000000 : ℝ)*X 2 1+(-848198239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_18 : ((933408893/5000000000 : ℝ)*X 0 0+(843020227/2500000000 : ℝ)*X 0 1+(6824900497/10000000000 : ℝ)*X 0 2+(933408893/5000000000 : ℝ)*X 1 0+(843020227/2500000000 : ℝ)*X 1 1+(6824900497/10000000000 : ℝ)*X 1 2+(933408893/5000000000 : ℝ)*X 2 0+(843020227/2500000000 : ℝ)*X 2 1+(6824900497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((-549261669/1250000000 : ℝ)*X 0 0+(1252526883/5000000000 : ℝ)*X 0 1+(1354933209/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1137827827/2500000000 : ℝ)*X 1 0+(-1525242821/5000000000 : ℝ)*X 1 1+(2399692151/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((81450491/200000000 : ℝ)*X 2 0+(6803709299/10000000000 : ℝ)*X 2 1+(-201454937/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((922959053/5000000000 : ℝ)*X 0 0+(3625593743/10000000000 : ℝ)*X 0 1+(6624748743/10000000000 : ℝ)*X 0 2+(922959053/5000000000 : ℝ)*X 1 0+(3625593743/10000000000 : ℝ)*X 1 1+(6624748743/10000000000 : ℝ)*X 1 2+(922959053/5000000000 : ℝ)*X 2 0+(3625593743/10000000000 : ℝ)*X 2 1+(6624748743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((16287/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16287/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6576095366013686719029/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2347166797/20000000000 : ℝ)*(base40) + (2595124737199/1000000000000 : ℝ)*(base49) + (31944185437/8000000000 : ℝ)*(base59) + (8992225263/20000000000 : ℝ)*(base60) + (2045040883727/200000000000 : ℝ)*(major_s0_0) + (2045040883727/200000000000 : ℝ)*(major_s0_1) + (2045040883727/200000000000 : ℝ)*(major_s0_2) + (689322911/1000000000000 : ℝ)*(sp_s0_0) + (101383331/1000000000000 : ℝ)*(sp_s0_2) + (7462634051201/500000000000 : ℝ)*(sp_s0_7) + (14926073886767/1000000000000 : ℝ)*(sp_s0_8) + (3731493125859/250000000000 : ℝ)*(sp_s0_9) + (2762165283217/500000000000 : ℝ)*(sp_s0_12) + (116461453/1000000000000 : ℝ)*(sp_s0_19) + (2762165283217/500000000000 : ℝ)*(f.failure) + (14926073886767/1000000000000 : ℝ)*(f.sum) + (136171570126913/500000000000000000000000000 : ℝ)*base62 + (1374542518489831/2000000000000000000000000000 : ℝ)*base65 + (1594540801997483/2000000000000000000000000000 : ℝ)*base67 + (798657436402517/2000000000000000000000000000 : ℝ)*base69 + (267867646443657/1000000000000000000000000000 : ℝ)*base71 + (13396901510169/2000000000000000000000000000 : ℝ)*base73 + (1267358262489831/2000000000000000000000000000 : ℝ)*base75 + (1212817625597483/2000000000000000000000000000 : ℝ)*base77 + (201914991123087/500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (8699/25000000000000000 : ℝ)*base87 + (8699/25000000000000000 : ℝ)*base89 + (8699/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((20223/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(20223/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1362385359087955812957/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (265259265211/250000000000 : ℝ)*(base40) + (328833956909/100000000000 : ℝ)*(base49) + (2700201825847/500000000000 : ℝ)*(base59) + (224493045271/1000000000000 : ℝ)*(base60) + (2846314140797/200000000000 : ℝ)*(major_s0_0) + (2846314140797/200000000000 : ℝ)*(major_s0_1) + (2846314140797/200000000000 : ℝ)*(major_s0_2) + (14737989/250000000000 : ℝ)*(sp_s0_7) + (420083/8000000000 : ℝ)*(sp_s0_8) + (20774246023273/1000000000000 : ℝ)*(sp_s0_13) + (20774252464853/1000000000000 : ℝ)*(sp_s0_14) + (20774160173001/1000000000000 : ℝ)*(sp_s0_15) + (7688834162093/1000000000000 : ℝ)*(sp_s0_18) + (144802227/1000000000000 : ℝ)*(sp_s0_21) + (7688834162093/1000000000000 : ℝ)*(f.failure) + (5193576243807/250000000000 : ℝ)*(f.sum) + (105773499087757/500000000000000000000000000 : ℝ)*base63 + (73794327942459/2000000000000000000000000000 : ℝ)*base64 + (40544027093487/2000000000000000000000000000 : ℝ)*base66 + (1367746376493487/2000000000000000000000000000 : ℝ)*base69 + (358190700117973/1000000000000000000000000000 : ℝ)*base70 + (1523336816942459/2000000000000000000000000000 : ℝ)*base73 + (157713980142459/2000000000000000000000000000 : ℝ)*base74 + (518665812906513/2000000000000000000000000000 : ℝ)*base77 + (205657518962243/500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (29129/50000000000000000 : ℝ)*base86 + (29129/50000000000000000 : ℝ)*base88 + (29129/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1957/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1957/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17486479480114272255453/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224944175031/500000000000 : ℝ)*(base40) + (1216806952633/500000000000 : ℝ)*(base49) + (3990915949649/1000000000000 : ℝ)*(base59) + (2934798933219/250000000000 : ℝ)*(major_s0_0) + (2934798933219/250000000000 : ℝ)*(major_s0_1) + (2934798933219/250000000000 : ℝ)*(major_s0_2) + (33923591/500000000000 : ℝ)*(sp_s0_0) + (173983329/1000000000000 : ℝ)*(sp_s0_6) + (96292791/31250000000 : ℝ)*(sp_s0_12) + (2064631/12500000000 : ℝ)*(sp_s0_14) + (8568015158413/500000000000 : ℝ)*(sp_s0_19) + (17135932993527/1000000000000 : ℝ)*(sp_s0_20) + (17136098164007/1000000000000 : ℝ)*(sp_s0_21) + (3169516643019/500000000000 : ℝ)*(sp_s0_25) + (6342288638679/1000000000000 : ℝ)*(f.failure) + (17136098164007/1000000000000 : ℝ)*(f.sum) + (158059251319639/625000000000000000000000000 : ℝ)*base63 + (1769966996636293/2500000000000000000000000000 : ℝ)*base64 + (1684854697414849/2500000000000000000000000000 : ℝ)*base66 + (25074124585151/2500000000000000000000000000 : ℝ)*base68 + (159113217400571/1250000000000000000000000000 : ℝ)*base70 + (1308400832613707/2500000000000000000000000000 : ℝ)*base72 + (183512397386293/2500000000000000000000000000 : ℝ)*base74 + (877885582585151/2500000000000000000000000000 : ℝ)*base77 + (360612270132139/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (25413/50000000000000000 : ℝ)*base87 + (25413/50000000000000000 : ℝ)*base89 + (25413/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (16287/100000 : ℝ) ^ (79/16 : ℝ) ≤ (6418527668826051/50000000000000000000 : ℝ) := by
    have hpowers : (16287/100000 : ℝ)^79 ≤ (6418527668826051/50000000000000000000 : ℝ)^16 := by
      have hnat : (16287 : ℕ)^79*50000000000000000000^16 ≤ 6418527668826051^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16287 100000 6418527668826051 50000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16287/100000 : ℝ)) (X := (6418527668826051/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50006418527668826051/50000000000000000000 : ℝ) ≤ (625016248605461/625000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (50006418527668826051/50000000000000000000 : ℝ)^16 ≤ (625016248605461/625000000000000 : ℝ)^79 := by
      have hnat : (50006418527668826051 : ℕ)^16*625000000000000^79 ≤ 625016248605461^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006418527668826051 50000000000000000000 625016248605461 625000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625016248605461/625000000000000 : ℝ)) (X := (50006418527668826051/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25006418527668826051/25000000000000000000 : ℝ) ≤ (2500129982191309/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (25006418527668826051/25000000000000000000 : ℝ)^16 ≤ (2500129982191309/2500000000000000 : ℝ)^79 := by
      have hnat : (25006418527668826051 : ℕ)^16*2500000000000000^79 ≤ 2500129982191309^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006418527668826051 25000000000000000000 2500129982191309 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500129982191309/2500000000000000 : ℝ)) (X := (25006418527668826051/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(16248605461/101793750000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12997553893/81435000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (16287/100000 : ℝ)) (alpha := (16248605461/101793750000000 : ℝ)) (beta := (12997553893/81435000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16287/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(16248605461/101793750000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12997553893/81435000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (20223/100000 : ℝ) ^ (79/16 : ℝ) ≤ (9344424708342621/25000000000000000000 : ℝ) := by
    have hpowers : (20223/100000 : ℝ)^79 ≤ (9344424708342621/25000000000000000000 : ℝ)^16 := by
      have hnat : (20223 : ℕ)^79*25000000000000000000^16 ≤ 9344424708342621^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20223 100000 9344424708342621 25000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20223/100000 : ℝ)) (X := (9344424708342621/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25009344424708342621/25000000000000000000 : ℝ) ≤ (5000378451943249/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (25009344424708342621/25000000000000000000 : ℝ)^16 ≤ (5000378451943249/5000000000000000 : ℝ)^79 := by
      have hnat : (25009344424708342621 : ℕ)^16*5000000000000000^79 ≤ 5000378451943249^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009344424708342621 25000000000000000000 5000378451943249 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000378451943249/5000000000000000 : ℝ)) (X := (25009344424708342621/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12509344424708342621/12500000000000000000 : ℝ) ≤ (2500378395569129/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (12509344424708342621/12500000000000000000 : ℝ)^16 ≤ (2500378395569129/2500000000000000 : ℝ)^79 := by
      have hnat : (12509344424708342621 : ℕ)^16*2500000000000000^79 ≤ 2500378395569129^79*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509344424708342621 12500000000000000000 2500378395569129 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500378395569129/2500000000000000 : ℝ)) (X := (12509344424708342621/12500000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(378451943249/1011150000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(126113065003/337050000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (20223/100000 : ℝ)) (alpha := (378451943249/1011150000000000 : ℝ)) (beta := (126113065003/337050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (20223/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(378451943249/1011150000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(126113065003/337050000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1957/100000 : ℝ) ^ (79/16 : ℝ) ≤ (183526890337/50000000000000000000 : ℝ) := by
    have hpowers : (1957/100000 : ℝ)^79 ≤ (183526890337/50000000000000000000 : ℝ)^16 := by
      have hnat : (1957 : ℕ)^79*50000000000000000000^16 ≤ 183526890337^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1957 100000 183526890337 50000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1957/100000 : ℝ)) (X := (183526890337/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50000000183526890337/50000000000000000000 : ℝ) ≤ (10000000007434001/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (50000000183526890337/50000000000000000000 : ℝ)^16 ≤ (10000000007434001/10000000000000000 : ℝ)^79 := by
      have hnat : (50000000183526890337 : ℕ)^16*10000000000000000^79 ≤ 10000000007434001^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000183526890337 50000000000000000000 10000000007434001 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000007434001/10000000000000000 : ℝ)) (X := (50000000183526890337/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25000000183526890337/25000000000000000000 : ℝ) ≤ (5000000007434001/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (25000000183526890337/25000000000000000000 : ℝ)^16 ≤ (5000000007434001/5000000000000000 : ℝ)^79 := by
      have hnat : (25000000183526890337 : ℕ)^16*5000000000000000^79 ≤ 5000000007434001^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000183526890337 25000000000000000000 5000000007434001 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000007434001/5000000000000000 : ℝ)) (X := (25000000183526890337/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(7434001/195700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(7434001/195700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1957/100000 : ℝ)) (alpha := (7434001/195700000000000 : ℝ)) (beta := (7434001/195700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1957/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(7434001/195700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(7434001/195700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-425429399/1000000000 : ℝ)*X 0 0+(3286857331/10000000000 : ℝ)*X 0 1+(195073649/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1103049493/2500000000 : ℝ)*X 1 0+(-3408853569/10000000000 : ℝ)*X 1 1+(184425973/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4180122983/10000000000 : ℝ)*X 2 0+(1436832749/2500000000 : ℝ)*X 2 1+(-587066177/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1431007963/5000000000 : ℝ)*X 0 0+(3935040407/10000000000 : ℝ)*X 0 1+(2774852107/5000000000 : ℝ)*X 0 2+(1431007963/5000000000 : ℝ)*X 1 0+(3935040407/10000000000 : ℝ)*X 1 1+(2774852107/5000000000 : ℝ)*X 1 2+(1431007963/5000000000 : ℝ)*X 2 0+(3935040407/10000000000 : ℝ)*X 2 1+(2774852107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319081_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-23167712995362819726522391373/2904515000000000000000000000 : ℝ) := by norm_num
    linear_combination (32013/125000000000 : ℝ)*(base23) + (98699/1000000000000 : ℝ)*(base24) + (18141/500000000000 : ℝ)*(base39) + (70378210317/1000000000000 : ℝ)*(base40) + (452628210529/1000000000000 : ℝ)*(base49) + (9189/1000000000000 : ℝ)*(base50) + (97513707191/100000000000 : ℝ)*(base59) + (195808037031/500000000000 : ℝ)*(base60) + (92547/50000 : ℝ)*(major_s1_0) + (92547/50000 : ℝ)*(major_s1_1) + (92547/50000 : ℝ)*(major_s1_2) + (2658816015219/1000000000000 : ℝ)*(sp_s1_0) + (2658816015219/1000000000000 : ℝ)*(sp_s1_1) + (20771997347/7812500000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2658816015219/1000000000000 : ℝ)*(f.sum) + (75981203441981/209399000000000000000000000 : ℝ)*base62 + (11422907003027/19570000000000000000000000 : ℝ)*base65 + (49278573949/128400000000000000000000 : ℝ)*base67 + (870017373419/4892500000000000000000000 : ℝ)*base68 + (19041903181299883/106245530000000000000000000000 : ℝ)*base71 + (1385422920677/2171600000000000000000000 : ℝ)*base73 + (477838443/8359375000000000000000 : ℝ)*base75 + (4708652363/106035156250000000000000 : ℝ)*base77 + (79931170075517/68074570312500000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p019_b041 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 81 ≤ c.val) (hhi : c.val < 82)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=81 := by omega
  rcases hc with rfl
  · exact collision_c319081 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 81 ≤ c.val) (hhi : c.val < 82)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019_b041 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
