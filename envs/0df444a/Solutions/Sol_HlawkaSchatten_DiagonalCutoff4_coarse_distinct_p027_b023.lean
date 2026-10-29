-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b023
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:15:06.675411+00:00
-- url     : https://prove2.me/submissions/26854beb-cbf9-4a70-8283-b630ad9485ab

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
theorem collision_support_c327050_s0_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-76772731/312500000 : ℝ)*x 0 + (1228363757/5000000000 : ℝ)*x 1 + (-1721259413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76772731/312500000 : ℝ)^91 ≤ (9104787044491/50000000000000 : ℝ)^75 := by
    have hnat : (76772731 : ℕ)^91*50000000000000^75 ≤ 9104787044491^75*312500000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76772731 312500000 9104787044491 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1228363757/5000000000 : ℝ)^91 ≤ (9104787593087/50000000000000 : ℝ)^75 := by
    have hnat : (1228363757 : ℕ)^91*50000000000000^75 ≤ 9104787593087^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228363757 5000000000 9104787593087 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1721259413/2500000000 : ℝ)^91 ≤ (63580850709679/100000000000000 : ℝ)^75 := by
    have hnat : (1721259413 : ℕ)^91*100000000000000^75 ≤ 63580850709679^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721259413 2500000000 63580850709679 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-76772731/312500000 : ℝ), (1228363757/5000000000 : ℝ), (-1721259413/2500000000 : ℝ)] ![(9104787044491/50000000000000 : ℝ), (9104787593087/50000000000000 : ℝ), (63580850709679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-76772731/312500000 : ℝ)|^91 ≤ (9104787044491/50000000000000 : ℝ)^75
        have hw : |(-76772731/312500000 : ℝ)|=(76772731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1228363757/5000000000 : ℝ)|^91 ≤ (9104787593087/50000000000000 : ℝ)^75
        have hw : |(1228363757/5000000000 : ℝ)|=(1228363757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1721259413/2500000000 : ℝ)|^91 ≤ (63580850709679/100000000000000 : ℝ)^75
        have hw : |(-1721259413/2500000000 : ℝ)|=(1721259413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3112227881/10000000000 : ℝ)*x 0 + (-622445627/2000000000 : ℝ)*x 1 + (-5785109843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3112227881/10000000000 : ℝ)^91 ≤ (24262001134381/100000000000000 : ℝ)^75 := by
    have hnat : (3112227881 : ℕ)^91*100000000000000^75 ≤ 24262001134381^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3112227881 10000000000 24262001134381 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (622445627/2000000000 : ℝ)^91 ≤ (24262003536913/100000000000000 : ℝ)^75 := by
    have hnat : (622445627 : ℕ)^91*100000000000000^75 ≤ 24262003536913^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622445627 2000000000 24262003536913 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5785109843/10000000000 : ℝ)^91 ≤ (51475995321901/100000000000000 : ℝ)^75 := by
    have hnat : (5785109843 : ℕ)^91*100000000000000^75 ≤ 51475995321901^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5785109843 10000000000 51475995321901 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3112227881/10000000000 : ℝ), (-622445627/2000000000 : ℝ), (-5785109843/10000000000 : ℝ)] ![(24262001134381/100000000000000 : ℝ), (24262003536913/100000000000000 : ℝ), (51475995321901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3112227881/10000000000 : ℝ)|^91 ≤ (24262001134381/100000000000000 : ℝ)^75
        have hw : |(3112227881/10000000000 : ℝ)|=(3112227881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-622445627/2000000000 : ℝ)|^91 ≤ (24262003536913/100000000000000 : ℝ)^75
        have hw : |(-622445627/2000000000 : ℝ)|=(622445627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5785109843/10000000000 : ℝ)|^91 ≤ (51475995321901/100000000000000 : ℝ)^75
        have hw : |(-5785109843/10000000000 : ℝ)|=(5785109843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1362524007/10000000000 : ℝ)*x 0 + (288280757/5000000000 : ℝ)*x 1 + (-4498219513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1362524007/10000000000 : ℝ)^91 ≤ (8905758577749/100000000000000 : ℝ)^75 := by
    have hnat : (1362524007 : ℕ)^91*100000000000000^75 ≤ 8905758577749^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362524007 10000000000 8905758577749 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288280757/5000000000 : ℝ)^91 ≤ (784210639303/25000000000000 : ℝ)^75 := by
    have hnat : (288280757 : ℕ)^91*25000000000000^75 ≤ 784210639303^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288280757 5000000000 784210639303 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498219513/5000000000 : ℝ)^91 ≤ (87957398849077/100000000000000 : ℝ)^75 := by
    have hnat : (4498219513 : ℕ)^91*100000000000000^75 ≤ 87957398849077^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498219513 5000000000 87957398849077 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1362524007/10000000000 : ℝ), (288280757/5000000000 : ℝ), (-4498219513/5000000000 : ℝ)] ![(8905758577749/100000000000000 : ℝ), (784210639303/25000000000000 : ℝ), (87957398849077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1362524007/10000000000 : ℝ)|^91 ≤ (8905758577749/100000000000000 : ℝ)^75
        have hw : |(-1362524007/10000000000 : ℝ)|=(1362524007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(288280757/5000000000 : ℝ)|^91 ≤ (784210639303/25000000000000 : ℝ)^75
        have hw : |(288280757/5000000000 : ℝ)|=(288280757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4498219513/5000000000 : ℝ)|^91 ≤ (87957398849077/100000000000000 : ℝ)^75
        have hw : |(-4498219513/5000000000 : ℝ)|=(4498219513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1303457347/5000000000 : ℝ)*x 0 + (-712162467/5000000000 : ℝ)*x 1 + (-1885889611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1303457347/5000000000 : ℝ)^91 ≤ (19568935791403/100000000000000 : ℝ)^75 := by
    have hnat : (1303457347 : ℕ)^91*100000000000000^75 ≤ 19568935791403^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303457347 5000000000 19568935791403 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (712162467/5000000000 : ℝ)^91 ≤ (9398221581379/100000000000000 : ℝ)^75 := by
    have hnat : (712162467 : ℕ)^91*100000000000000^75 ≤ 9398221581379^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712162467 5000000000 9398221581379 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1885889611/2500000000 : ℝ)^91 ≤ (14206568522551/20000000000000 : ℝ)^75 := by
    have hnat : (1885889611 : ℕ)^91*20000000000000^75 ≤ 14206568522551^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885889611 2500000000 14206568522551 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1303457347/5000000000 : ℝ), (-712162467/5000000000 : ℝ), (-1885889611/2500000000 : ℝ)] ![(19568935791403/100000000000000 : ℝ), (9398221581379/100000000000000 : ℝ), (14206568522551/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1303457347/5000000000 : ℝ)|^91 ≤ (19568935791403/100000000000000 : ℝ)^75
        have hw : |(1303457347/5000000000 : ℝ)|=(1303457347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-712162467/5000000000 : ℝ)|^91 ≤ (9398221581379/100000000000000 : ℝ)^75
        have hw : |(-712162467/5000000000 : ℝ)|=(712162467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1885889611/2500000000 : ℝ)|^91 ≤ (14206568522551/20000000000000 : ℝ)^75
        have hw : |(-1885889611/2500000000 : ℝ)|=(1885889611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1214509769/2500000000 : ℝ)*x 0 + (6330761267/10000000000 : ℝ)*x 1 + (10576403/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1214509769/2500000000 : ℝ)^91 ≤ (20822970741971/50000000000000 : ℝ)^75 := by
    have hnat : (1214509769 : ℕ)^91*50000000000000^75 ≤ 20822970741971^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214509769 2500000000 20822970741971 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6330761267/10000000000 : ℝ)^91 ≤ (2296994001483/4000000000000 : ℝ)^75 := by
    have hnat : (6330761267 : ℕ)^91*4000000000000^75 ≤ 2296994001483^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6330761267 10000000000 2296994001483 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10576403/500000000 : ℝ)^91 ≤ (929208463367/100000000000000 : ℝ)^75 := by
    have hnat : (10576403 : ℕ)^91*100000000000000^75 ≤ 929208463367^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10576403 500000000 929208463367 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1214509769/2500000000 : ℝ), (6330761267/10000000000 : ℝ), (10576403/500000000 : ℝ)] ![(20822970741971/50000000000000 : ℝ), (2296994001483/4000000000000 : ℝ), (929208463367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1214509769/2500000000 : ℝ)|^91 ≤ (20822970741971/50000000000000 : ℝ)^75
        have hw : |(1214509769/2500000000 : ℝ)|=(1214509769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6330761267/10000000000 : ℝ)|^91 ≤ (2296994001483/4000000000000 : ℝ)^75
        have hw : |(6330761267/10000000000 : ℝ)|=(6330761267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10576403/500000000 : ℝ)|^91 ≤ (929208463367/100000000000000 : ℝ)^75
        have hw : |(10576403/500000000 : ℝ)|=(10576403/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1440366813/10000000000 : ℝ)*x 0 + (9124529137/10000000000 : ℝ)*x 1 + (-44722549/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1440366813/10000000000 : ℝ)^91 ≤ (9526807043449/100000000000000 : ℝ)^75 := by
    have hnat : (1440366813 : ℕ)^91*100000000000000^75 ≤ 9526807043449^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440366813 10000000000 9526807043449 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9124529137/10000000000 : ℝ)^91 ≤ (89479186619571/100000000000000 : ℝ)^75 := by
    have hnat : (9124529137 : ℕ)^91*100000000000000^75 ≤ 89479186619571^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9124529137 10000000000 89479186619571 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44722549/2000000000 : ℝ)^91 ≤ (497003165907/50000000000000 : ℝ)^75 := by
    have hnat : (44722549 : ℕ)^91*50000000000000^75 ≤ 497003165907^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44722549 2000000000 497003165907 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1440366813/10000000000 : ℝ), (9124529137/10000000000 : ℝ), (-44722549/2000000000 : ℝ)] ![(9526807043449/100000000000000 : ℝ), (89479186619571/100000000000000 : ℝ), (497003165907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1440366813/10000000000 : ℝ)|^91 ≤ (9526807043449/100000000000000 : ℝ)^75
        have hw : |(1440366813/10000000000 : ℝ)|=(1440366813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9124529137/10000000000 : ℝ)|^91 ≤ (89479186619571/100000000000000 : ℝ)^75
        have hw : |(9124529137/10000000000 : ℝ)|=(9124529137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44722549/2000000000 : ℝ)|^91 ≤ (497003165907/50000000000000 : ℝ)^75
        have hw : |(-44722549/2000000000 : ℝ)|=(44722549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-204302823/2000000000 : ℝ)*x 0 + (80713517/500000000 : ℝ)*x 1 + (-4278894401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204302823/2000000000 : ℝ)^91 ≤ (6278894288349/100000000000000 : ℝ)^75 := by
    have hnat : (204302823 : ℕ)^91*100000000000000^75 ≤ 6278894288349^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204302823 2000000000 6278894288349 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80713517/500000000 : ℝ)^91 ≤ (1367480736801/12500000000000 : ℝ)^75 := by
    have hnat : (80713517 : ℕ)^91*12500000000000^75 ≤ 1367480736801^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80713517 500000000 1367480736801 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4278894401/5000000000 : ℝ)^91 ≤ (41390629897303/50000000000000 : ℝ)^75 := by
    have hnat : (4278894401 : ℕ)^91*50000000000000^75 ≤ 41390629897303^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278894401 5000000000 41390629897303 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204302823/2000000000 : ℝ), (80713517/500000000 : ℝ), (-4278894401/5000000000 : ℝ)] ![(6278894288349/100000000000000 : ℝ), (1367480736801/12500000000000 : ℝ), (41390629897303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204302823/2000000000 : ℝ)|^91 ≤ (6278894288349/100000000000000 : ℝ)^75
        have hw : |(-204302823/2000000000 : ℝ)|=(204302823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80713517/500000000 : ℝ)|^91 ≤ (1367480736801/12500000000000 : ℝ)^75
        have hw : |(80713517/500000000 : ℝ)|=(80713517/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4278894401/5000000000 : ℝ)|^91 ≤ (41390629897303/50000000000000 : ℝ)^75
        have hw : |(-4278894401/5000000000 : ℝ)|=(4278894401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1792756497/10000000000 : ℝ)*x 0 + (-711267169/2500000000 : ℝ)*x 1 + (-177100043/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1792756497/10000000000 : ℝ)^91 ≤ (6212158402169/50000000000000 : ℝ)^75 := by
    have hnat : (1792756497 : ℕ)^91*50000000000000^75 ≤ 6212158402169^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792756497 10000000000 6212158402169 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (711267169/2500000000 : ℝ)^91 ≤ (5439669956299/25000000000000 : ℝ)^75 := by
    have hnat : (711267169 : ℕ)^91*25000000000000^75 ≤ 5439669956299^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711267169 2500000000 5439669956299 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177100043/250000000 : ℝ)^91 ≤ (65817003354389/100000000000000 : ℝ)^75 := by
    have hnat : (177100043 : ℕ)^91*100000000000000^75 ≤ 65817003354389^75*250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177100043 250000000 65817003354389 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1792756497/10000000000 : ℝ), (-711267169/2500000000 : ℝ), (-177100043/250000000 : ℝ)] ![(6212158402169/50000000000000 : ℝ), (5439669956299/25000000000000 : ℝ), (65817003354389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1792756497/10000000000 : ℝ)|^91 ≤ (6212158402169/50000000000000 : ℝ)^75
        have hw : |(1792756497/10000000000 : ℝ)|=(1792756497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-711267169/2500000000 : ℝ)|^91 ≤ (5439669956299/25000000000000 : ℝ)^75
        have hw : |(-711267169/2500000000 : ℝ)|=(711267169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-177100043/250000000 : ℝ)|^91 ≤ (65817003354389/100000000000000 : ℝ)^75
        have hw : |(-177100043/250000000 : ℝ)|=(177100043/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_16 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7406581061/10000000000 : ℝ)*x 0 + (3727089157/10000000000 : ℝ)*x 1 + (5696339/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7406581061/10000000000 : ℝ)^91 ≤ (69470897050011/100000000000000 : ℝ)^75 := by
    have hnat : (7406581061 : ℕ)^91*100000000000000^75 ≤ 69470897050011^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7406581061 10000000000 69470897050011 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3727089157/10000000000 : ℝ)^91 ≤ (30194557440637/100000000000000 : ℝ)^75 := by
    have hnat : (3727089157 : ℕ)^91*100000000000000^75 ≤ 30194557440637^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3727089157 10000000000 30194557440637 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5696339/625000000 : ℝ)^91 ≤ (167272746137/50000000000000 : ℝ)^75 := by
    have hnat : (5696339 : ℕ)^91*50000000000000^75 ≤ 167272746137^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5696339 625000000 167272746137 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7406581061/10000000000 : ℝ), (3727089157/10000000000 : ℝ), (5696339/625000000 : ℝ)] ![(69470897050011/100000000000000 : ℝ), (30194557440637/100000000000000 : ℝ), (167272746137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7406581061/10000000000 : ℝ)|^91 ≤ (69470897050011/100000000000000 : ℝ)^75
        have hw : |(7406581061/10000000000 : ℝ)|=(7406581061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3727089157/10000000000 : ℝ)|^91 ≤ (30194557440637/100000000000000 : ℝ)^75
        have hw : |(3727089157/10000000000 : ℝ)|=(3727089157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5696339/625000000 : ℝ)|^91 ≤ (167272746137/50000000000000 : ℝ)^75
        have hw : |(5696339/625000000 : ℝ)|=(5696339/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1827146749/2500000000 : ℝ)*x 0 + (3784829629/10000000000 : ℝ)*x 1 + (-101096861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1827146749/2500000000 : ℝ)^91 ≤ (17089311233709/25000000000000 : ℝ)^75 := by
    have hnat : (1827146749 : ℕ)^91*25000000000000^75 ≤ 17089311233709^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827146749 2500000000 17089311233709 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3784829629/10000000000 : ℝ)^91 ≤ (7690765362023/25000000000000 : ℝ)^75 := by
    have hnat : (3784829629 : ℕ)^91*25000000000000^75 ≤ 7690765362023^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3784829629 10000000000 7690765362023 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101096861/5000000000 : ℝ)^91 ≤ (439846803467/50000000000000 : ℝ)^75 := by
    have hnat : (101096861 : ℕ)^91*50000000000000^75 ≤ 439846803467^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101096861 5000000000 439846803467 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1827146749/2500000000 : ℝ), (3784829629/10000000000 : ℝ), (-101096861/5000000000 : ℝ)] ![(17089311233709/25000000000000 : ℝ), (7690765362023/25000000000000 : ℝ), (439846803467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1827146749/2500000000 : ℝ)|^91 ≤ (17089311233709/25000000000000 : ℝ)^75
        have hw : |(1827146749/2500000000 : ℝ)|=(1827146749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3784829629/10000000000 : ℝ)|^91 ≤ (7690765362023/25000000000000 : ℝ)^75
        have hw : |(3784829629/10000000000 : ℝ)|=(3784829629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101096861/5000000000 : ℝ)|^91 ≤ (439846803467/50000000000000 : ℝ)^75
        have hw : |(-101096861/5000000000 : ℝ)|=(101096861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3778206973/10000000000 : ℝ)*x 0 + (1106107993/5000000000 : ℝ)*x 1 + (-743820219/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3778206973/10000000000 : ℝ)^91 ≤ (3837220157339/12500000000000 : ℝ)^75 := by
    have hnat : (3778206973 : ℕ)^91*12500000000000^75 ≤ 3837220157339^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3778206973 10000000000 3837220157339 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106107993/5000000000 : ℝ)^91 ≤ (16034572978683/100000000000000 : ℝ)^75 := by
    have hnat : (1106107993 : ℕ)^91*100000000000000^75 ≤ 16034572978683^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106107993 5000000000 16034572978683 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743820219/1250000000 : ℝ)^91 ≤ (53267665754309/100000000000000 : ℝ)^75 := by
    have hnat : (743820219 : ℕ)^91*100000000000000^75 ≤ 53267665754309^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743820219 1250000000 53267665754309 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3778206973/10000000000 : ℝ), (1106107993/5000000000 : ℝ), (-743820219/1250000000 : ℝ)] ![(3837220157339/12500000000000 : ℝ), (16034572978683/100000000000000 : ℝ), (53267665754309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3778206973/10000000000 : ℝ)|^91 ≤ (3837220157339/12500000000000 : ℝ)^75
        have hw : |(-3778206973/10000000000 : ℝ)|=(3778206973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1106107993/5000000000 : ℝ)|^91 ≤ (16034572978683/100000000000000 : ℝ)^75
        have hw : |(1106107993/5000000000 : ℝ)|=(1106107993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-743820219/1250000000 : ℝ)|^91 ≤ (53267665754309/100000000000000 : ℝ)^75
        have hw : |(-743820219/1250000000 : ℝ)|=(743820219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_22 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1522706123/5000000000 : ℝ)*x 0 + (-3398259669/10000000000 : ℝ)*x 1 + (-349362929/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1522706123/5000000000 : ℝ)^91 ≤ (23631461895943/100000000000000 : ℝ)^75 := by
    have hnat : (1522706123 : ℕ)^91*100000000000000^75 ≤ 23631461895943^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522706123 5000000000 23631461895943 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3398259669/10000000000 : ℝ)^91 ≤ (1079736921603/4000000000000 : ℝ)^75 := by
    have hnat : (3398259669 : ℕ)^91*4000000000000^75 ≤ 1079736921603^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3398259669 10000000000 1079736921603 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349362929/625000000 : ℝ)^91 ≤ (49375115042907/100000000000000 : ℝ)^75 := by
    have hnat : (349362929 : ℕ)^91*100000000000000^75 ≤ 49375115042907^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349362929 625000000 49375115042907 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1522706123/5000000000 : ℝ), (-3398259669/10000000000 : ℝ), (-349362929/625000000 : ℝ)] ![(23631461895943/100000000000000 : ℝ), (1079736921603/4000000000000 : ℝ), (49375115042907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1522706123/5000000000 : ℝ)|^91 ≤ (23631461895943/100000000000000 : ℝ)^75
        have hw : |(1522706123/5000000000 : ℝ)|=(1522706123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3398259669/10000000000 : ℝ)|^91 ≤ (1079736921603/4000000000000 : ℝ)^75
        have hw : |(-3398259669/10000000000 : ℝ)|=(3398259669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-349362929/625000000 : ℝ)|^91 ≤ (49375115042907/100000000000000 : ℝ)^75
        have hw : |(-349362929/625000000 : ℝ)|=(349362929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_23 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8255084553/10000000000 : ℝ)*x 0 + (512040563/2000000000 : ℝ)*x 1 + (333372037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8255084553/10000000000 : ℝ)^91 ≤ (79242004232919/100000000000000 : ℝ)^75 := by
    have hnat : (8255084553 : ℕ)^91*100000000000000^75 ≤ 79242004232919^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8255084553 10000000000 79242004232919 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512040563/2000000000 : ℝ)^91 ≤ (153154427719/800000000000 : ℝ)^75 := by
    have hnat : (512040563 : ℕ)^91*800000000000^75 ≤ 153154427719^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512040563 2000000000 153154427719 800000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333372037/10000000000 : ℝ)^91 ≤ (100855768289/6250000000000 : ℝ)^75 := by
    have hnat : (333372037 : ℕ)^91*6250000000000^75 ≤ 100855768289^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333372037 10000000000 100855768289 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8255084553/10000000000 : ℝ), (512040563/2000000000 : ℝ), (333372037/10000000000 : ℝ)] ![(79242004232919/100000000000000 : ℝ), (153154427719/800000000000 : ℝ), (100855768289/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8255084553/10000000000 : ℝ)|^91 ≤ (79242004232919/100000000000000 : ℝ)^75
        have hw : |(8255084553/10000000000 : ℝ)|=(8255084553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512040563/2000000000 : ℝ)|^91 ≤ (153154427719/800000000000 : ℝ)^75
        have hw : |(512040563/2000000000 : ℝ)|=(512040563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(333372037/10000000000 : ℝ)|^91 ≤ (100855768289/6250000000000 : ℝ)^75
        have hw : |(333372037/10000000000 : ℝ)|=(333372037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s0_27 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5461157/312500000 : ℝ)*x 0 + (9854251479/10000000000 : ℝ)*x 1 + (-230011327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5461157/312500000 : ℝ)^91 ≤ (368516865019/50000000000000 : ℝ)^75 := by
    have hnat : (5461157 : ℕ)^91*50000000000000^75 ≤ 368516865019^75*312500000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461157 312500000 368516865019 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9854251479/10000000000 : ℝ)^91 ≤ (49117172228341/50000000000000 : ℝ)^75 := by
    have hnat : (9854251479 : ℕ)^91*50000000000000^75 ≤ 49117172228341^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9854251479 10000000000 49117172228341 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230011327/10000000000 : ℝ)^91 ≤ (1028621800739/100000000000000 : ℝ)^75 := by
    have hnat : (230011327 : ℕ)^91*100000000000000^75 ≤ 1028621800739^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230011327 10000000000 1028621800739 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5461157/312500000 : ℝ), (9854251479/10000000000 : ℝ), (-230011327/10000000000 : ℝ)] ![(368516865019/50000000000000 : ℝ), (49117172228341/50000000000000 : ℝ), (1028621800739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5461157/312500000 : ℝ)|^91 ≤ (368516865019/50000000000000 : ℝ)^75
        have hw : |(5461157/312500000 : ℝ)|=(5461157/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9854251479/10000000000 : ℝ)|^91 ≤ (49117172228341/50000000000000 : ℝ)^75
        have hw : |(9854251479/10000000000 : ℝ)|=(9854251479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-230011327/10000000000 : ℝ)|^91 ≤ (1028621800739/100000000000000 : ℝ)^75
        have hw : |(-230011327/10000000000 : ℝ)|=(230011327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s1_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3011596301/10000000000 : ℝ)*x 0 + (1498007947/5000000000 : ℝ)*x 1 + (-1194744743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3011596301/10000000000 : ℝ)^91 ≤ (23313459816799/100000000000000 : ℝ)^75 := by
    have hnat : (3011596301 : ℕ)^91*100000000000000^75 ≤ 23313459816799^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3011596301 10000000000 23313459816799 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1498007947/5000000000 : ℝ)^91 ≤ (23167198711943/100000000000000 : ℝ)^75 := by
    have hnat : (1498007947 : ℕ)^91*100000000000000^75 ≤ 23167198711943^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498007947 5000000000 23167198711943 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194744743/2000000000 : ℝ)^91 ≤ (13379835363589/25000000000000 : ℝ)^75 := by
    have hnat : (1194744743 : ℕ)^91*25000000000000^75 ≤ 13379835363589^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194744743 2000000000 13379835363589 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3011596301/10000000000 : ℝ), (1498007947/5000000000 : ℝ), (-1194744743/2000000000 : ℝ)] ![(23313459816799/100000000000000 : ℝ), (23167198711943/100000000000000 : ℝ), (13379835363589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3011596301/10000000000 : ℝ)|^91 ≤ (23313459816799/100000000000000 : ℝ)^75
        have hw : |(-3011596301/10000000000 : ℝ)|=(3011596301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1498007947/5000000000 : ℝ)|^91 ≤ (23167198711943/100000000000000 : ℝ)^75
        have hw : |(1498007947/5000000000 : ℝ)|=(1498007947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1194744743/2000000000 : ℝ)|^91 ≤ (13379835363589/25000000000000 : ℝ)^75
        have hw : |(-1194744743/2000000000 : ℝ)|=(1194744743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s1_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3485112137/10000000000 : ℝ)*x 0 + (-693147091/2000000000 : ℝ)*x 1 + (-5132922369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3485112137/10000000000 : ℝ)^91 ≤ (27832763622291/100000000000000 : ℝ)^75 := by
    have hnat : (3485112137 : ℕ)^91*100000000000000^75 ≤ 27832763622291^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3485112137 10000000000 27832763622291 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693147091/2000000000 : ℝ)^91 ≤ (13822558423791/50000000000000 : ℝ)^75 := by
    have hnat : (693147091 : ℕ)^91*50000000000000^75 ≤ 13822558423791^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693147091 2000000000 13822558423791 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5132922369/10000000000 : ℝ)^91 ≤ (44522119514701/100000000000000 : ℝ)^75 := by
    have hnat : (5132922369 : ℕ)^91*100000000000000^75 ≤ 44522119514701^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132922369 10000000000 44522119514701 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3485112137/10000000000 : ℝ), (-693147091/2000000000 : ℝ), (-5132922369/10000000000 : ℝ)] ![(27832763622291/100000000000000 : ℝ), (13822558423791/50000000000000 : ℝ), (44522119514701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3485112137/10000000000 : ℝ)|^91 ≤ (27832763622291/100000000000000 : ℝ)^75
        have hw : |(3485112137/10000000000 : ℝ)|=(3485112137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-693147091/2000000000 : ℝ)|^91 ≤ (13822558423791/50000000000000 : ℝ)^75
        have hw : |(-693147091/2000000000 : ℝ)|=(693147091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5132922369/10000000000 : ℝ)|^91 ≤ (44522119514701/100000000000000 : ℝ)^75
        have hw : |(-5132922369/10000000000 : ℝ)|=(5132922369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s1_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (549357459/1000000000 : ℝ)*x 0 + (77491323/156250000 : ℝ)*x 1 + (684132557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549357459/1000000000 : ℝ)^91 ≤ (48345653053983/100000000000000 : ℝ)^75 := by
    have hnat : (549357459 : ℕ)^91*100000000000000^75 ≤ 48345653053983^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549357459 1000000000 48345653053983 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77491323/156250000 : ℝ)^91 ≤ (21351518701799/50000000000000 : ℝ)^75 := by
    have hnat : (77491323 : ℕ)^91*50000000000000^75 ≤ 21351518701799^75*156250000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77491323 156250000 21351518701799 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684132557/5000000000 : ℝ)^91 ≤ (4475654764923/50000000000000 : ℝ)^75 := by
    have hnat : (684132557 : ℕ)^91*50000000000000^75 ≤ 4475654764923^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684132557 5000000000 4475654764923 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(549357459/1000000000 : ℝ), (77491323/156250000 : ℝ), (684132557/5000000000 : ℝ)] ![(48345653053983/100000000000000 : ℝ), (21351518701799/50000000000000 : ℝ), (4475654764923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(549357459/1000000000 : ℝ)|^91 ≤ (48345653053983/100000000000000 : ℝ)^75
        have hw : |(549357459/1000000000 : ℝ)|=(549357459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77491323/156250000 : ℝ)|^91 ≤ (21351518701799/50000000000000 : ℝ)^75
        have hw : |(77491323/156250000 : ℝ)|=(77491323/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684132557/5000000000 : ℝ)|^91 ≤ (4475654764923/50000000000000 : ℝ)^75
        have hw : |(684132557/5000000000 : ℝ)|=(684132557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327050_s1_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (975482971/2500000000 : ℝ)*x 0 + (286272427/500000000 : ℝ)*x 1 + (-1174521739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975482971/2500000000 : ℝ)^91 ≤ (3990212540233/12500000000000 : ℝ)^75 := by
    have hnat : (975482971 : ℕ)^91*12500000000000^75 ≤ 3990212540233^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975482971 2500000000 3990212540233 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286272427/500000000 : ℝ)^91 ≤ (6354073369921/12500000000000 : ℝ)^75 := by
    have hnat : (286272427 : ℕ)^91*12500000000000^75 ≤ 6354073369921^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286272427 500000000 6354073369921 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174521739/5000000000 : ℝ)^91 ≤ (4311428175653/25000000000000 : ℝ)^75 := by
    have hnat : (1174521739 : ℕ)^91*25000000000000^75 ≤ 4311428175653^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174521739 5000000000 4311428175653 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(975482971/2500000000 : ℝ), (286272427/500000000 : ℝ), (-1174521739/5000000000 : ℝ)] ![(3990212540233/12500000000000 : ℝ), (6354073369921/12500000000000 : ℝ), (4311428175653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(975482971/2500000000 : ℝ)|^91 ≤ (3990212540233/12500000000000 : ℝ)^75
        have hw : |(975482971/2500000000 : ℝ)|=(975482971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(286272427/500000000 : ℝ)|^91 ≤ (6354073369921/12500000000000 : ℝ)^75
        have hw : |(286272427/500000000 : ℝ)|=(286272427/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1174521739/5000000000 : ℝ)|^91 ≤ (4311428175653/25000000000000 : ℝ)^75
        have hw : |(-1174521739/5000000000 : ℝ)|=(1174521739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327050 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (32523/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-76772731/312500000 : ℝ)*X 0 0+(1228363757/5000000000 : ℝ)*X 0 1+(-1721259413/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3112227881/10000000000 : ℝ)*X 1 0+(-622445627/2000000000 : ℝ)*X 1 1+(-5785109843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1362524007/10000000000 : ℝ)*X 0 0+(288280757/5000000000 : ℝ)*X 0 1+(-4498219513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1303457347/5000000000 : ℝ)*X 1 0+(-712162467/5000000000 : ℝ)*X 1 1+(-1885889611/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1214509769/2500000000 : ℝ)*X 2 0+(6330761267/10000000000 : ℝ)*X 2 1+(10576403/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1440366813/10000000000 : ℝ)*X 0 0+(9124529137/10000000000 : ℝ)*X 0 1+(-44722549/2000000000 : ℝ)*X 0 2+(1440366813/10000000000 : ℝ)*X 1 0+(9124529137/10000000000 : ℝ)*X 1 1+(-44722549/2000000000 : ℝ)*X 1 2+(1440366813/10000000000 : ℝ)*X 2 0+(9124529137/10000000000 : ℝ)*X 2 1+(-44722549/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-204302823/2000000000 : ℝ)*X 0 0+(80713517/500000000 : ℝ)*X 0 1+(-4278894401/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1792756497/10000000000 : ℝ)*X 1 0+(-711267169/2500000000 : ℝ)*X 1 1+(-177100043/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7406581061/10000000000 : ℝ)*X 2 0+(3727089157/10000000000 : ℝ)*X 2 1+(5696339/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1827146749/2500000000 : ℝ)*X 0 0+(3784829629/10000000000 : ℝ)*X 0 1+(-101096861/5000000000 : ℝ)*X 0 2+(1827146749/2500000000 : ℝ)*X 1 0+(3784829629/10000000000 : ℝ)*X 1 1+(-101096861/5000000000 : ℝ)*X 1 2+(1827146749/2500000000 : ℝ)*X 2 0+(3784829629/10000000000 : ℝ)*X 2 1+(-101096861/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-3778206973/10000000000 : ℝ)*X 0 0+(1106107993/5000000000 : ℝ)*X 0 1+(-743820219/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1522706123/5000000000 : ℝ)*X 1 0+(-3398259669/10000000000 : ℝ)*X 1 1+(-349362929/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((8255084553/10000000000 : ℝ)*X 2 0+(512040563/2000000000 : ℝ)*X 2 1+(333372037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((5461157/312500000 : ℝ)*X 0 0+(9854251479/10000000000 : ℝ)*X 0 1+(-230011327/10000000000 : ℝ)*X 0 2+(5461157/312500000 : ℝ)*X 1 0+(9854251479/10000000000 : ℝ)*X 1 1+(-230011327/10000000000 : ℝ)*X 1 2+(5461157/312500000 : ℝ)*X 2 0+(9854251479/10000000000 : ℝ)*X 2 1+(-230011327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1581/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1581/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (74209711828053981/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (509000728539/500000000000 : ℝ)*(base7) + (80337/500000000000 : ℝ)*(base39) + (1819307/1000000000000 : ℝ)*(base53) + (2513749/1000000000000 : ℝ)*(base60) + (1583834391227/1000000000000 : ℝ)*(major_s0_0) + (1583834391227/1000000000000 : ℝ)*(major_s0_1) + (1583832571919/1000000000000 : ℝ)*(major_s0_2) + (933689551011/500000000000 : ℝ)*(sp_s0_7) + (1867373489547/1000000000000 : ℝ)*(sp_s0_8) + (933696781119/500000000000 : ℝ)*(sp_s0_9) + (883225080467/500000000000 : ℝ)*(sp_s0_13) + (12640909/1000000000000 : ℝ)*(sp_s0_14) + (2281673/125000000000 : ℝ)*(sp_s0_15) + (2044111/125000000000 : ℝ)*(sp_s0_27) + (93558132093/125000000000 : ℝ)*(f.failure) + (933696781119/500000000000 : ℝ)*(f.sum) + (50937049818099/625000000000000000000000000 : ℝ)*base62 + (516505110159107/5000000000000000000000000000 : ℝ)*base65 + (3187783456960769/5000000000000000000000000000 : ℝ)*base67 + (503295976030003/2500000000000000000000000000 : ℝ)*base69 + (533146892945691/5000000000000000000000000000 : ℝ)*base70 + (5781391218039231/5000000000000000000000000000 : ℝ)*base73 + (827832600447601/2500000000000000000000000000 : ℝ)*base75 + (842605071947601/2500000000000000000000000000 : ℝ)*base77 + (2459633963/5000000000000000000000 : ℝ)*base79 + (5677/12500000000000000 : ℝ)*base86 + (5677/12500000000000000 : ℝ)*base88 + (6823/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59331/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29178895693701296547951/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (762895462591/500000000000 : ℝ)*(base5) + (474360274827/500000000000 : ℝ)*(base7) + (29424360327/1000000000000 : ℝ)*(base39) + (249751125523/250000000000 : ℝ)*(base60) + (1955232331511/1000000000000 : ℝ)*(major_s0_0) + (1955232331511/1000000000000 : ℝ)*(major_s0_1) + (1955232331511/1000000000000 : ℝ)*(major_s0_2) + (2220301/500000000000 : ℝ)*(sp_s0_0) + (17404197/1000000000000 : ℝ)*(sp_s0_1) + (31226317/1000000000000 : ℝ)*(sp_s0_8) + (1236113774847/500000000000 : ℝ)*(sp_s0_14) + (1236091679891/500000000000 : ℝ)*(sp_s0_15) + (3998022915479/1000000000000 : ℝ)*(sp_s0_16) + (173452216367/500000000000 : ℝ)*(sp_s0_20) + (461987404131/500000000000 : ℝ)*(f.failure) + (309028998787/125000000000 : ℝ)*(f.sum) + (161382627/1000000000000000000000 : ℝ)*base62 + (3466835128900683/5000000000000000000000000000 : ℝ)*base65 + (4530688145900683/5000000000000000000000000000 : ℝ)*base66 + (1096471162076907/2500000000000000000000000000 : ℝ)*base69 + (261197514746869/5000000000000000000000000000 : ℝ)*base71 + (3232875930599317/5000000000000000000000000000 : ℝ)*base72 + (83726051076907/2500000000000000000000000000 : ℝ)*base74 + (627582297423093/2500000000000000000000000000 : ℝ)*base77 + (349598463/2500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (15041/50000000000000000 : ℝ)*base87 + (15041/50000000000000000 : ℝ)*base89 + (15041/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-47699/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-47699/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3182581113961793114247/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (163351012181/250000000000 : ℝ)*(base7) + (928569/200000000000 : ℝ)*(base33) + (65621/40000000000 : ℝ)*(base39) + (166320100379/500000000000 : ℝ)*(base44) + (3330945783/100000000000 : ℝ)*(base50) + (4738137/1000000000000 : ℝ)*(base60) + (2022119424893/1000000000000 : ℝ)*(major_s0_0) + (84474193349/50000000000 : ℝ)*(major_s0_1) + (1011062033869/500000000000 : ℝ)*(major_s0_2) + (11818261/250000000000 : ℝ)*(sp_s0_16) + (1367241416221/500000000000 : ℝ)*(sp_s0_21) + (2401837988839/1000000000000 : ℝ)*(sp_s0_22) + (2734430916553/1000000000000 : ℝ)*(sp_s0_23) + (1276349364663/1000000000000 : ℝ)*(sp_s0_27) + (955585516697/1000000000000 : ℝ)*(f.failure) + (1367241416221/500000000000 : ℝ)*(f.sum) + (423679110293023/1250000000000000000000000000 : ℝ)*base63 + (1851423419362457/2500000000000000000000000000 : ℝ)*base65 + (36572068447897/250000000000000000000000000 : ℝ)*base66 + (277776042322153/1250000000000000000000000000 : ℝ)*base69 + (61491028307763/78125000000000000000000000 : ℝ)*base71 + (1547405716532871/5000000000000000000000000000 : ℝ)*base72 + (72186054015413/125000000000000000000000000 : ℝ)*base74 + (814484665735959/2500000000000000000000000000 : ℝ)*base77 + (2043192184490811/5000000000000000000000000000 : ℝ)*base78 + (31133/100000000000000000 : ℝ)*base86 + (31133/100000000000000000 : ℝ)*base88 + (31133/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (1581/2500 : ℝ) ^ (89/16 : ℝ) ≤ (7816588120140980289/100000000000000000000 : ℝ) := by
    have hpowers : (1581/2500 : ℝ)^89 ≤ (7816588120140980289/100000000000000000000 : ℝ)^16 := by
      have hnat : (1581 : ℕ)^89*100000000000000000000^16 ≤ 7816588120140980289^16*2500^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1581 2500 7816588120140980289 100000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1581/2500 : ℝ)) (X := (7816588120140980289/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (107816588120140980289/100000000000000000000 : ℝ) ≤ (5068110374088703/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (107816588120140980289/100000000000000000000 : ℝ)^16 ≤ (5068110374088703/5000000000000000 : ℝ)^89 := by
      have hnat : (107816588120140980289 : ℕ)^16*5000000000000000^89 ≤ 5068110374088703^89*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107816588120140980289 100000000000000000000 5068110374088703 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5068110374088703/5000000000000000 : ℝ)) (X := (107816588120140980289/100000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (57816588120140980289/50000000000000000000 : ℝ) ≤ (10264567762284997/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (57816588120140980289/50000000000000000000 : ℝ)^16 ≤ (10264567762284997/10000000000000000 : ℝ)^89 := by
      have hnat : (57816588120140980289 : ℕ)^16*10000000000000000^89 ≤ 10264567762284997^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57816588120140980289 50000000000000000000 10264567762284997 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10264567762284997/10000000000000000 : ℝ)) (X := (57816588120140980289/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(68110374088703/3162000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(128347014107591/6324000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1581/2500 : ℝ)) (alpha := (68110374088703/3162000000000000 : ℝ)) (beta := (128347014107591/6324000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1581/2500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(68110374088703/3162000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(128347014107591/6324000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (59331/100000 : ℝ) ^ (89/16 : ℝ) ≤ (5481245822044649421/100000000000000000000 : ℝ) := by
    have hpowers : (59331/100000 : ℝ)^89 ≤ (5481245822044649421/100000000000000000000 : ℝ)^16 := by
      have hnat : (59331 : ℕ)^89*100000000000000000000^16 ≤ 5481245822044649421^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59331 100000 5481245822044649421 100000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59331/100000 : ℝ)) (X := (5481245822044649421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (105481245822044649421/100000000000000000000 : ℝ) ≤ (5048197547582159/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (105481245822044649421/100000000000000000000 : ℝ)^16 ≤ (5048197547582159/5000000000000000 : ℝ)^89 := by
      have hnat : (105481245822044649421 : ℕ)^16*5000000000000000^89 ≤ 5048197547582159^89*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105481245822044649421 100000000000000000000 5048197547582159 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048197547582159/5000000000000000 : ℝ)) (X := (105481245822044649421/100000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (55481245822044649421/50000000000000000000 : ℝ) ≤ (5094382717706227/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (55481245822044649421/50000000000000000000 : ℝ)^16 ≤ (5094382717706227/5000000000000000 : ℝ)^89 := by
      have hnat : (55481245822044649421 : ℕ)^16*5000000000000000^89 ≤ 5094382717706227^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55481245822044649421 50000000000000000000 5094382717706227 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5094382717706227/5000000000000000 : ℝ)) (X := (55481245822044649421/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(16065849194053/988850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(11546292531017/741637500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (59331/100000 : ℝ)) (alpha := (16065849194053/988850000000000 : ℝ)) (beta := (11546292531017/741637500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (59331/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(16065849194053/988850000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(11546292531017/741637500000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (47699/100000 : ℝ) ^ (89/16 : ℝ) ≤ (814100164106667231/50000000000000000000 : ℝ) := by
    have hpowers : (47699/100000 : ℝ)^89 ≤ (814100164106667231/50000000000000000000 : ℝ)^16 := by
      have hnat : (47699 : ℕ)^89*50000000000000000000^16 ≤ 814100164106667231^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47699 100000 814100164106667231 50000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47699/100000 : ℝ)) (X := (814100164106667231/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50814100164106667231/50000000000000000000 : ℝ) ≤ (5014538735183737/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (50814100164106667231/50000000000000000000 : ℝ)^16 ≤ (5014538735183737/5000000000000000 : ℝ)^89 := by
      have hnat : (50814100164106667231 : ℕ)^16*5000000000000000^89 ≤ 5014538735183737^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50814100164106667231 50000000000000000000 5014538735183737 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014538735183737/5000000000000000 : ℝ)) (X := (50814100164106667231/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25814100164106667231/25000000000000000000 : ℝ) ≤ (1257221914039823/1250000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (25814100164106667231/25000000000000000000 : ℝ)^16 ≤ (1257221914039823/1250000000000000 : ℝ)^89 := by
      have hnat : (25814100164106667231 : ℕ)^16*1250000000000000^89 ≤ 1257221914039823^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25814100164106667231 25000000000000000000 1257221914039823 1250000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257221914039823/1250000000000000 : ℝ)) (X := (25814100164106667231/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(14538735183737/2384950000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(2869784195111/476990000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (47699/100000 : ℝ)) (alpha := (14538735183737/2384950000000000 : ℝ)) (beta := (2869784195111/476990000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (47699/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(14538735183737/2384950000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(2869784195111/476990000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3011596301/10000000000 : ℝ)*X 0 0+(1498007947/5000000000 : ℝ)*X 0 1+(-1194744743/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3485112137/10000000000 : ℝ)*X 1 0+(-693147091/2000000000 : ℝ)*X 1 1+(-5132922369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((549357459/1000000000 : ℝ)*X 2 0+(77491323/156250000 : ℝ)*X 2 1+(684132557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((975482971/2500000000 : ℝ)*X 0 0+(286272427/500000000 : ℝ)*X 0 1+(-1174521739/5000000000 : ℝ)*X 0 2+(975482971/2500000000 : ℝ)*X 1 0+(286272427/500000000 : ℝ)*X 1 1+(-1174521739/5000000000 : ℝ)*X 1 2+(975482971/2500000000 : ℝ)*X 2 0+(286272427/500000000 : ℝ)*X 2 1+(-1174521739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327050_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-484833/50000 : ℝ) < ((-211611/100000 : ℝ)*P 0+(-211611/100000 : ℝ)*P 1+(-211611/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-484833/50000 : ℝ) < (-12082091409915191859930365576409/1256868650000000000000000000000 : ℝ) := by norm_num
    linear_combination (192299/1000000000000 : ℝ)*(base5) + (69743/1000000000000 : ℝ)*(base16) + (4467/1000000000000 : ℝ)*(base18) + (7007/200000000000 : ℝ)*(base21) + (193524724807/1000000000000 : ℝ)*(base39) + (97773/500000000000 : ℝ)*(base53) + (596288282171/1000000000000 : ℝ)*(base60) + (27161/1000000000000 : ℝ)*(ratio_s0_1) + (211611/100000 : ℝ)*(major_s1_0) + (211611/100000 : ℝ)*(major_s1_1) + (1058054902227/500000000000 : ℝ)*(major_s1_2) + (200267722761/62500000000 : ℝ)*(sp_s1_0) + (640856697993/200000000000 : ℝ)*(sp_s1_1) + (1602141958493/500000000000 : ℝ)*(sp_s1_2) + (999999807701/1000000000000 : ℝ)*(sp_s1_6) + (1602141879861/500000000000 : ℝ)*(f.sum) + (24991864353837307467/23583578075000000000000000000000 : ℝ)*base63 + (56342840738739/238495000000000000000000000 : ℝ)*base65 + (1627563022143/98885000000000000000000000 : ℝ)*base67 + (1320645100728347/2384950000000000000000000000 : ℝ)*base69 + (94654522519146193/251373730000000000000000000000 : ℝ)*base71 + (5328823962099/5270000000000000000000000 : ℝ)*base72 + (1425940779181/24721250000000000000000000 : ℝ)*base74 + (173932463641/1317500000000000000000000 : ℝ)*base76 + (31696011061555577/52112395000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p027_b023 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 50 ≤ c.val) (hhi : c.val < 51)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=50 := by omega
  rcases hc with rfl
  · exact collision_c327050 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 50 ≤ c.val) (hhi : c.val < 51)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b023 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
