-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b043
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:57:21.94976+00:00
-- url     : https://prove2.me/submissions/e6f85266-1a25-44e1-ba31-8b846034fc06

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
theorem collision_support_c324083_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1682709367/10000000000 : ℝ)*x 0 + (4726226199/10000000000 : ℝ)*x 1 + (1123551043/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1682709367/10000000000 : ℝ)^85 ≤ (11130968773923/100000000000000 : ℝ)^69 := by
    have hnat : (1682709367 : ℕ)^85*100000000000000^69 ≤ 11130968773923^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682709367 10000000000 11130968773923 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4726226199/10000000000 : ℝ)^85 ≤ (19861388651243/50000000000000 : ℝ)^69 := by
    have hnat : (4726226199 : ℕ)^85*50000000000000^69 ≤ 19861388651243^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4726226199 10000000000 19861388651243 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123551043/2000000000 : ℝ)^85 ≤ (49146253907547/100000000000000 : ℝ)^69 := by
    have hnat : (1123551043 : ℕ)^85*100000000000000^69 ≤ 49146253907547^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123551043 2000000000 49146253907547 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1682709367/10000000000 : ℝ), (4726226199/10000000000 : ℝ), (1123551043/2000000000 : ℝ)] ![(11130968773923/100000000000000 : ℝ), (19861388651243/50000000000000 : ℝ), (49146253907547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1682709367/10000000000 : ℝ)|^85 ≤ (11130968773923/100000000000000 : ℝ)^69
        have hw : |(-1682709367/10000000000 : ℝ)|=(1682709367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4726226199/10000000000 : ℝ)|^85 ≤ (19861388651243/50000000000000 : ℝ)^69
        have hw : |(4726226199/10000000000 : ℝ)|=(4726226199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123551043/2000000000 : ℝ)|^85 ≤ (49146253907547/100000000000000 : ℝ)^69
        have hw : |(1123551043/2000000000 : ℝ)|=(1123551043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (422556007/1250000000 : ℝ)*x 0 + (6888933757/10000000000 : ℝ)*x 1 + (-100506847/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422556007/1250000000 : ℝ)^85 ≤ (26287598231039/100000000000000 : ℝ)^69 := by
    have hnat : (422556007 : ℕ)^85*100000000000000^69 ≤ 26287598231039^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422556007 1250000000 26287598231039 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6888933757/10000000000 : ℝ)^85 ≤ (63186171170651/100000000000000 : ℝ)^69 := by
    have hnat : (6888933757 : ℕ)^85*100000000000000^69 ≤ 63186171170651^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6888933757 10000000000 63186171170651 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100506847/625000000 : ℝ)^85 ≤ (10526230589429/100000000000000 : ℝ)^69 := by
    have hnat : (100506847 : ℕ)^85*100000000000000^69 ≤ 10526230589429^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100506847 625000000 10526230589429 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422556007/1250000000 : ℝ), (6888933757/10000000000 : ℝ), (-100506847/625000000 : ℝ)] ![(26287598231039/100000000000000 : ℝ), (63186171170651/100000000000000 : ℝ), (10526230589429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422556007/1250000000 : ℝ)|^85 ≤ (26287598231039/100000000000000 : ℝ)^69
        have hw : |(422556007/1250000000 : ℝ)|=(422556007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6888933757/10000000000 : ℝ)|^85 ≤ (63186171170651/100000000000000 : ℝ)^69
        have hw : |(6888933757/10000000000 : ℝ)|=(6888933757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100506847/625000000 : ℝ)|^85 ≤ (10526230589429/100000000000000 : ℝ)^69
        have hw : |(-100506847/625000000 : ℝ)|=(100506847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3049055321/10000000000 : ℝ)*x 0 + (263232663/1250000000 : ℝ)*x 1 + (135988127/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3049055321/10000000000 : ℝ)^85 ≤ (289375310667/1250000000000 : ℝ)^69 := by
    have hnat : (3049055321 : ℕ)^85*1250000000000^69 ≤ 289375310667^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3049055321 10000000000 289375310667 1250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263232663/1250000000 : ℝ)^85 ≤ (733692225139/5000000000000 : ℝ)^69 := by
    have hnat : (263232663 : ℕ)^85*5000000000000^69 ≤ 733692225139^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263232663 1250000000 733692225139 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135988127/200000000 : ℝ)^85 ≤ (621761306281/1000000000000 : ℝ)^69 := by
    have hnat : (135988127 : ℕ)^85*1000000000000^69 ≤ 621761306281^69*200000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135988127 200000000 621761306281 1000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3049055321/10000000000 : ℝ), (263232663/1250000000 : ℝ), (135988127/200000000 : ℝ)] ![(289375310667/1250000000000 : ℝ), (733692225139/5000000000000 : ℝ), (621761306281/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3049055321/10000000000 : ℝ)|^85 ≤ (289375310667/1250000000000 : ℝ)^69
        have hw : |(-3049055321/10000000000 : ℝ)|=(3049055321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263232663/1250000000 : ℝ)|^85 ≤ (733692225139/5000000000000 : ℝ)^69
        have hw : |(263232663/1250000000 : ℝ)|=(263232663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135988127/200000000 : ℝ)|^85 ≤ (621761306281/1000000000000 : ℝ)^69
        have hw : |(135988127/200000000 : ℝ)|=(135988127/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2515016087/5000000000 : ℝ)*x 0 + (118231/5000000000 : ℝ)*x 1 + (1586492119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2515016087/5000000000 : ℝ)^85 ≤ (670177443529/1562500000000 : ℝ)^69 := by
    have hnat : (2515016087 : ℕ)^85*1562500000000^69 ≤ 670177443529^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515016087 5000000000 670177443529 1562500000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118231/5000000000 : ℝ)^85 ≤ (99995481/50000000000000 : ℝ)^69 := by
    have hnat : (118231 : ℕ)^85*50000000000000^69 ≤ 99995481^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118231 5000000000 99995481 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586492119/2500000000 : ℝ)^85 ≤ (57108443608869/100000000000000 : ℝ)^69 := by
    have hnat : (1586492119 : ℕ)^85*100000000000000^69 ≤ 57108443608869^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586492119 2500000000 57108443608869 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2515016087/5000000000 : ℝ), (118231/5000000000 : ℝ), (1586492119/2500000000 : ℝ)] ![(670177443529/1562500000000 : ℝ), (99995481/50000000000000 : ℝ), (57108443608869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2515016087/5000000000 : ℝ)|^85 ≤ (670177443529/1562500000000 : ℝ)^69
        have hw : |(2515016087/5000000000 : ℝ)|=(2515016087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(118231/5000000000 : ℝ)|^85 ≤ (99995481/50000000000000 : ℝ)^69
        have hw : |(118231/5000000000 : ℝ)|=(118231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1586492119/2500000000 : ℝ)|^85 ≤ (57108443608869/100000000000000 : ℝ)^69
        have hw : |(1586492119/2500000000 : ℝ)|=(1586492119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (125694063/1250000000 : ℝ)*x 0 + (3400049/3906250 : ℝ)*x 1 + (-1518990653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125694063/1250000000 : ℝ)^85 ≤ (2951537611299/50000000000000 : ℝ)^69 := by
    have hnat : (125694063 : ℕ)^85*50000000000000^69 ≤ 2951537611299^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125694063 1250000000 2951537611299 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3400049/3906250 : ℝ)^85 ≤ (658473638169/781250000000 : ℝ)^69 := by
    have hnat : (3400049 : ℕ)^85*781250000000^69 ≤ 658473638169^69*3906250^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3400049 3906250 658473638169 781250000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1518990653/10000000000 : ℝ)^85 ≤ (9812299082099/100000000000000 : ℝ)^69 := by
    have hnat : (1518990653 : ℕ)^85*100000000000000^69 ≤ 9812299082099^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518990653 10000000000 9812299082099 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(125694063/1250000000 : ℝ), (3400049/3906250 : ℝ), (-1518990653/10000000000 : ℝ)] ![(2951537611299/50000000000000 : ℝ), (658473638169/781250000000 : ℝ), (9812299082099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(125694063/1250000000 : ℝ)|^85 ≤ (2951537611299/50000000000000 : ℝ)^69
        have hw : |(125694063/1250000000 : ℝ)|=(125694063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3400049/3906250 : ℝ)|^85 ≤ (658473638169/781250000000 : ℝ)^69
        have hw : |(3400049/3906250 : ℝ)|=(3400049/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1518990653/10000000000 : ℝ)|^85 ≤ (9812299082099/100000000000000 : ℝ)^69
        have hw : |(-1518990653/10000000000 : ℝ)|=(1518990653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2107613827/10000000000 : ℝ)*x 0 + (3322356789/5000000000 : ℝ)*x 1 + (646401773/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107613827/10000000000 : ℝ)^85 ≤ (459027794159/3125000000000 : ℝ)^69 := by
    have hnat : (2107613827 : ℕ)^85*3125000000000^69 ≤ 459027794159^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107613827 10000000000 459027794159 3125000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3322356789/5000000000 : ℝ)^85 ≤ (60438174927919/100000000000000 : ℝ)^69 := by
    have hnat : (3322356789 : ℕ)^85*100000000000000^69 ≤ 60438174927919^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3322356789 5000000000 60438174927919 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646401773/2000000000 : ℝ)^85 ≤ (24872935640701/100000000000000 : ℝ)^69 := by
    have hnat : (646401773 : ℕ)^85*100000000000000^69 ≤ 24872935640701^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646401773 2000000000 24872935640701 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2107613827/10000000000 : ℝ), (3322356789/5000000000 : ℝ), (646401773/2000000000 : ℝ)] ![(459027794159/3125000000000 : ℝ), (60438174927919/100000000000000 : ℝ), (24872935640701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2107613827/10000000000 : ℝ)|^85 ≤ (459027794159/3125000000000 : ℝ)^69
        have hw : |(2107613827/10000000000 : ℝ)|=(2107613827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3322356789/5000000000 : ℝ)|^85 ≤ (60438174927919/100000000000000 : ℝ)^69
        have hw : |(3322356789/5000000000 : ℝ)|=(3322356789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646401773/2000000000 : ℝ)|^85 ≤ (24872935640701/100000000000000 : ℝ)^69
        have hw : |(646401773/2000000000 : ℝ)|=(646401773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-354079451/10000000000 : ℝ)*x 0 + (51945023/250000000 : ℝ)*x 1 + (8674793791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (354079451/10000000000 : ℝ)^85 ≤ (407943783881/25000000000000 : ℝ)^69 := by
    have hnat : (354079451 : ℕ)^85*25000000000000^69 ≤ 407943783881^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354079451 10000000000 407943783881 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51945023/250000000 : ℝ)^85 ≤ (14433350738641/100000000000000 : ℝ)^69 := by
    have hnat : (51945023 : ℕ)^85*100000000000000^69 ≤ 14433350738641^69*250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51945023 250000000 14433350738641 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8674793791/10000000000 : ℝ)^85 ≤ (2622964816097/3125000000000 : ℝ)^69 := by
    have hnat : (8674793791 : ℕ)^85*3125000000000^69 ≤ 2622964816097^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8674793791 10000000000 2622964816097 3125000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-354079451/10000000000 : ℝ), (51945023/250000000 : ℝ), (8674793791/10000000000 : ℝ)] ![(407943783881/25000000000000 : ℝ), (14433350738641/100000000000000 : ℝ), (2622964816097/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-354079451/10000000000 : ℝ)|^85 ≤ (407943783881/25000000000000 : ℝ)^69
        have hw : |(-354079451/10000000000 : ℝ)|=(354079451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51945023/250000000 : ℝ)|^85 ≤ (14433350738641/100000000000000 : ℝ)^69
        have hw : |(51945023/250000000 : ℝ)|=(51945023/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8674793791/10000000000 : ℝ)|^85 ≤ (2622964816097/3125000000000 : ℝ)^69
        have hw : |(8674793791/10000000000 : ℝ)|=(8674793791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9333372799/10000000000 : ℝ)*x 0 + (-2410823/10000000000 : ℝ)*x 1 + (40804331/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9333372799/10000000000 : ℝ)^85 ≤ (22963128372709/25000000000000 : ℝ)^69 := by
    have hnat : (9333372799 : ℕ)^85*25000000000000^69 ≤ 22963128372709^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9333372799 10000000000 22963128372709 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2410823/10000000000 : ℝ)^85 ≤ (3493390549/100000000000000 : ℝ)^69 := by
    have hnat : (2410823 : ℕ)^85*100000000000000^69 ≤ 3493390549^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2410823 10000000000 3493390549 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40804331/312500000 : ℝ)^85 ≤ (8143993105231/100000000000000 : ℝ)^69 := by
    have hnat : (40804331 : ℕ)^85*100000000000000^69 ≤ 8143993105231^69*312500000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40804331 312500000 8143993105231 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9333372799/10000000000 : ℝ), (-2410823/10000000000 : ℝ), (40804331/312500000 : ℝ)] ![(22963128372709/25000000000000 : ℝ), (3493390549/100000000000000 : ℝ), (8143993105231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9333372799/10000000000 : ℝ)|^85 ≤ (22963128372709/25000000000000 : ℝ)^69
        have hw : |(9333372799/10000000000 : ℝ)|=(9333372799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2410823/10000000000 : ℝ)|^85 ≤ (3493390549/100000000000000 : ℝ)^69
        have hw : |(-2410823/10000000000 : ℝ)|=(2410823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40804331/312500000 : ℝ)|^85 ≤ (8143993105231/100000000000000 : ℝ)^69
        have hw : |(40804331/312500000 : ℝ)|=(40804331/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1167921129/2500000000 : ℝ)*x 0 + (6373527581/10000000000 : ℝ)*x 1 + (-161674233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1167921129/2500000000 : ℝ)^85 ≤ (4894853466459/12500000000000 : ℝ)^69 := by
    have hnat : (1167921129 : ℕ)^85*12500000000000^69 ≤ 4894853466459^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167921129 2500000000 4894853466459 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6373527581/10000000000 : ℝ)^85 ≤ (57414115660901/100000000000000 : ℝ)^69 := by
    have hnat : (6373527581 : ℕ)^85*100000000000000^69 ≤ 57414115660901^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6373527581 10000000000 57414115660901 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161674233/2500000000 : ℝ)^85 ≤ (3427056591953/100000000000000 : ℝ)^69 := by
    have hnat : (161674233 : ℕ)^85*100000000000000^69 ≤ 3427056591953^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161674233 2500000000 3427056591953 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1167921129/2500000000 : ℝ), (6373527581/10000000000 : ℝ), (-161674233/2500000000 : ℝ)] ![(4894853466459/12500000000000 : ℝ), (57414115660901/100000000000000 : ℝ), (3427056591953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1167921129/2500000000 : ℝ)|^85 ≤ (4894853466459/12500000000000 : ℝ)^69
        have hw : |(1167921129/2500000000 : ℝ)|=(1167921129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6373527581/10000000000 : ℝ)|^85 ≤ (57414115660901/100000000000000 : ℝ)^69
        have hw : |(6373527581/10000000000 : ℝ)|=(6373527581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-161674233/2500000000 : ℝ)|^85 ≤ (3427056591953/100000000000000 : ℝ)^69
        have hw : |(-161674233/2500000000 : ℝ)|=(161674233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (560322623/2500000000 : ℝ)*x 0 + (129539959/500000000 : ℝ)*x 1 + (282712767/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (560322623/2500000000 : ℝ)^85 ≤ (15844882532137/100000000000000 : ℝ)^69 := by
    have hnat : (560322623 : ℕ)^85*100000000000000^69 ≤ 15844882532137^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560322623 2500000000 15844882532137 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129539959/500000000 : ℝ)^85 ≤ (189416753523/1000000000000 : ℝ)^69 := by
    have hnat : (129539959 : ℕ)^85*1000000000000^69 ≤ 189416753523^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129539959 500000000 189416753523 1000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282712767/400000000 : ℝ)^85 ≤ (16303360524281/25000000000000 : ℝ)^69 := by
    have hnat : (282712767 : ℕ)^85*25000000000000^69 ≤ 16303360524281^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282712767 400000000 16303360524281 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(560322623/2500000000 : ℝ), (129539959/500000000 : ℝ), (282712767/400000000 : ℝ)] ![(15844882532137/100000000000000 : ℝ), (189416753523/1000000000000 : ℝ), (16303360524281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(560322623/2500000000 : ℝ)|^85 ≤ (15844882532137/100000000000000 : ℝ)^69
        have hw : |(560322623/2500000000 : ℝ)|=(560322623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129539959/500000000 : ℝ)|^85 ≤ (189416753523/1000000000000 : ℝ)^69
        have hw : |(129539959/500000000 : ℝ)|=(129539959/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282712767/400000000 : ℝ)|^85 ≤ (16303360524281/25000000000000 : ℝ)^69
        have hw : |(282712767/400000000 : ℝ)|=(282712767/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1317664893/10000000000 : ℝ)*x 0 + (405937047/625000000 : ℝ)*x 1 + (406573439/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317664893/10000000000 : ℝ)^85 ≤ (4117861971161/50000000000000 : ℝ)^69 := by
    have hnat : (1317664893 : ℕ)^85*50000000000000^69 ≤ 4117861971161^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317664893 10000000000 4117861971161 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405937047/625000000 : ℝ)^85 ≤ (14691247019847/25000000000000 : ℝ)^69 := by
    have hnat : (405937047 : ℕ)^85*25000000000000^69 ≤ 14691247019847^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405937047 625000000 14691247019847 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406573439/1000000000 : ℝ)^85 ≤ (6599857594959/20000000000000 : ℝ)^69 := by
    have hnat : (406573439 : ℕ)^85*20000000000000^69 ≤ 6599857594959^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406573439 1000000000 6599857594959 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1317664893/10000000000 : ℝ), (405937047/625000000 : ℝ), (406573439/1000000000 : ℝ)] ![(4117861971161/50000000000000 : ℝ), (14691247019847/25000000000000 : ℝ), (6599857594959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1317664893/10000000000 : ℝ)|^85 ≤ (4117861971161/50000000000000 : ℝ)^69
        have hw : |(-1317664893/10000000000 : ℝ)|=(1317664893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(405937047/625000000 : ℝ)|^85 ≤ (14691247019847/25000000000000 : ℝ)^69
        have hw : |(405937047/625000000 : ℝ)|=(405937047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(406573439/1000000000 : ℝ)|^85 ≤ (6599857594959/20000000000000 : ℝ)^69
        have hw : |(406573439/1000000000 : ℝ)|=(406573439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8713603127/10000000000 : ℝ)*x 0 + (-2423/5000000000 : ℝ)*x 1 + (276674451/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8713603127/10000000000 : ℝ)^85 ≤ (84397696423811/100000000000000 : ℝ)^69 := by
    have hnat : (8713603127 : ℕ)^85*100000000000000^69 ≤ 84397696423811^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8713603127 10000000000 84397696423811 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2423/5000000000 : ℝ)^85 ≤ (166389/10000000000000 : ℝ)^69 := by
    have hnat : (2423 : ℕ)^85*10000000000000^69 ≤ 166389^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423 5000000000 166389 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276674451/1250000000 : ℝ)^85 ≤ (15602301903111/100000000000000 : ℝ)^69 := by
    have hnat : (276674451 : ℕ)^85*100000000000000^69 ≤ 15602301903111^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276674451 1250000000 15602301903111 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8713603127/10000000000 : ℝ), (-2423/5000000000 : ℝ), (276674451/1250000000 : ℝ)] ![(84397696423811/100000000000000 : ℝ), (166389/10000000000000 : ℝ), (15602301903111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8713603127/10000000000 : ℝ)|^85 ≤ (84397696423811/100000000000000 : ℝ)^69
        have hw : |(8713603127/10000000000 : ℝ)|=(8713603127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2423/5000000000 : ℝ)|^85 ≤ (166389/10000000000000 : ℝ)^69
        have hw : |(-2423/5000000000 : ℝ)|=(2423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276674451/1250000000 : ℝ)|^85 ≤ (15602301903111/100000000000000 : ℝ)^69
        have hw : |(276674451/1250000000 : ℝ)|=(276674451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_23 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (48345627/500000000 : ℝ)*x 0 + (2086832943/2500000000 : ℝ)*x 1 + (-1032630353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48345627/500000000 : ℝ)^85 ≤ (5624898079633/100000000000000 : ℝ)^69 := by
    have hnat : (48345627 : ℕ)^85*100000000000000^69 ≤ 5624898079633^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48345627 500000000 5624898079633 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086832943/2500000000 : ℝ)^85 ≤ (16009797084381/20000000000000 : ℝ)^69 := by
    have hnat : (2086832943 : ℕ)^85*20000000000000^69 ≤ 16009797084381^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086832943 2500000000 16009797084381 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032630353/5000000000 : ℝ)^85 ≤ (7163058241747/50000000000000 : ℝ)^69 := by
    have hnat : (1032630353 : ℕ)^85*50000000000000^69 ≤ 7163058241747^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032630353 5000000000 7163058241747 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(48345627/500000000 : ℝ), (2086832943/2500000000 : ℝ), (-1032630353/5000000000 : ℝ)] ![(5624898079633/100000000000000 : ℝ), (16009797084381/20000000000000 : ℝ), (7163058241747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(48345627/500000000 : ℝ)|^85 ≤ (5624898079633/100000000000000 : ℝ)^69
        have hw : |(48345627/500000000 : ℝ)|=(48345627/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2086832943/2500000000 : ℝ)|^85 ≤ (16009797084381/20000000000000 : ℝ)^69
        have hw : |(2086832943/2500000000 : ℝ)|=(2086832943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1032630353/5000000000 : ℝ)|^85 ≤ (7163058241747/50000000000000 : ℝ)^69
        have hw : |(-1032630353/5000000000 : ℝ)|=(1032630353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s0_27 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3237871759/5000000000 : ℝ)*x 0 + (155140123/500000000 : ℝ)*x 1 + (615705369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3237871759/5000000000 : ℝ)^85 ≤ (14637628612863/25000000000000 : ℝ)^69 := by
    have hnat : (3237871759 : ℕ)^85*25000000000000^69 ≤ 14637628612863^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3237871759 5000000000 14637628612863 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155140123/500000000 : ℝ)^85 ≤ (23653750504459/100000000000000 : ℝ)^69 := by
    have hnat : (155140123 : ℕ)^85*100000000000000^69 ≤ 23653750504459^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155140123 500000000 23653750504459 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (615705369/2500000000 : ℝ)^85 ≤ (8897867516247/50000000000000 : ℝ)^69 := by
    have hnat : (615705369 : ℕ)^85*50000000000000^69 ≤ 8897867516247^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615705369 2500000000 8897867516247 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3237871759/5000000000 : ℝ), (155140123/500000000 : ℝ), (615705369/2500000000 : ℝ)] ![(14637628612863/25000000000000 : ℝ), (23653750504459/100000000000000 : ℝ), (8897867516247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3237871759/5000000000 : ℝ)|^85 ≤ (14637628612863/25000000000000 : ℝ)^69
        have hw : |(3237871759/5000000000 : ℝ)|=(3237871759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(155140123/500000000 : ℝ)|^85 ≤ (23653750504459/100000000000000 : ℝ)^69
        have hw : |(155140123/500000000 : ℝ)|=(155140123/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(615705369/2500000000 : ℝ)|^85 ≤ (8897867516247/50000000000000 : ℝ)^69
        have hw : |(615705369/2500000000 : ℝ)|=(615705369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2311887053/10000000000 : ℝ)*x 0 + (4679663447/10000000000 : ℝ)*x 1 + (2581712613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2311887053/10000000000 : ℝ)^85 ≤ (514435145961/3125000000000 : ℝ)^69 := by
    have hnat : (2311887053 : ℕ)^85*3125000000000^69 ≤ 514435145961^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2311887053 10000000000 514435145961 3125000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4679663447/10000000000 : ℝ)^85 ≤ (39241233321713/100000000000000 : ℝ)^69 := by
    have hnat : (4679663447 : ℕ)^85*100000000000000^69 ≤ 39241233321713^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4679663447 10000000000 39241233321713 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2581712613/5000000000 : ℝ)^85 ≤ (5537105250263/12500000000000 : ℝ)^69 := by
    have hnat : (2581712613 : ℕ)^85*12500000000000^69 ≤ 5537105250263^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581712613 5000000000 5537105250263 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2311887053/10000000000 : ℝ), (4679663447/10000000000 : ℝ), (2581712613/5000000000 : ℝ)] ![(514435145961/3125000000000 : ℝ), (39241233321713/100000000000000 : ℝ), (5537105250263/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2311887053/10000000000 : ℝ)|^85 ≤ (514435145961/3125000000000 : ℝ)^69
        have hw : |(-2311887053/10000000000 : ℝ)|=(2311887053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4679663447/10000000000 : ℝ)|^85 ≤ (39241233321713/100000000000000 : ℝ)^69
        have hw : |(4679663447/10000000000 : ℝ)|=(4679663447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2581712613/5000000000 : ℝ)|^85 ≤ (5537105250263/12500000000000 : ℝ)^69
        have hw : |(2581712613/5000000000 : ℝ)|=(2581712613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s1_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3285690073/5000000000 : ℝ)*x 0 + (-189287003/2000000000 : ℝ)*x 1 + (4255216749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3285690073/5000000000 : ℝ)^85 ≤ (59617541370813/100000000000000 : ℝ)^69 := by
    have hnat : (3285690073 : ℕ)^85*100000000000000^69 ≤ 59617541370813^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3285690073 5000000000 59617541370813 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189287003/2000000000 : ℝ)^85 ≤ (5478511516951/100000000000000 : ℝ)^69 := by
    have hnat : (189287003 : ℕ)^85*100000000000000^69 ≤ 5478511516951^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189287003 2000000000 5478511516951 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4255216749/10000000000 : ℝ)^85 ≤ (17451973545041/50000000000000 : ℝ)^69 := by
    have hnat : (4255216749 : ℕ)^85*50000000000000^69 ≤ 17451973545041^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255216749 10000000000 17451973545041 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3285690073/5000000000 : ℝ), (-189287003/2000000000 : ℝ), (4255216749/10000000000 : ℝ)] ![(59617541370813/100000000000000 : ℝ), (5478511516951/100000000000000 : ℝ), (17451973545041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3285690073/5000000000 : ℝ)|^85 ≤ (59617541370813/100000000000000 : ℝ)^69
        have hw : |(3285690073/5000000000 : ℝ)|=(3285690073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-189287003/2000000000 : ℝ)|^85 ≤ (5478511516951/100000000000000 : ℝ)^69
        have hw : |(-189287003/2000000000 : ℝ)|=(189287003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4255216749/10000000000 : ℝ)|^85 ≤ (17451973545041/50000000000000 : ℝ)^69
        have hw : |(4255216749/10000000000 : ℝ)|=(4255216749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1757638973/5000000000 : ℝ)*x 0 + (1558955019/2500000000 : ℝ)*x 1 + (-231908217/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1757638973/5000000000 : ℝ)^85 ≤ (27585124931477/100000000000000 : ℝ)^69 := by
    have hnat : (1757638973 : ℕ)^85*100000000000000^69 ≤ 27585124931477^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757638973 5000000000 27585124931477 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1558955019/2500000000 : ℝ)^85 ≤ (27944907104731/50000000000000 : ℝ)^69 := by
    have hnat : (1558955019 : ℕ)^85*50000000000000^69 ≤ 27944907104731^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558955019 2500000000 27944907104731 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231908217/1000000000 : ℝ)^85 ≤ (3305012168633/20000000000000 : ℝ)^69 := by
    have hnat : (231908217 : ℕ)^85*20000000000000^69 ≤ 3305012168633^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231908217 1000000000 3305012168633 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1757638973/5000000000 : ℝ), (1558955019/2500000000 : ℝ), (-231908217/1000000000 : ℝ)] ![(27585124931477/100000000000000 : ℝ), (27944907104731/50000000000000 : ℝ), (3305012168633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1757638973/5000000000 : ℝ)|^85 ≤ (27585124931477/100000000000000 : ℝ)^69
        have hw : |(1757638973/5000000000 : ℝ)|=(1757638973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1558955019/2500000000 : ℝ)|^85 ≤ (27944907104731/50000000000000 : ℝ)^69
        have hw : |(1558955019/2500000000 : ℝ)|=(1558955019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-231908217/1000000000 : ℝ)|^85 ≤ (3305012168633/20000000000000 : ℝ)^69
        have hw : |(-231908217/1000000000 : ℝ)|=(231908217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324083_s1_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2894221147/10000000000 : ℝ)*x 0 + (4485355367/10000000000 : ℝ)*x 1 + (1213401159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2894221147/10000000000 : ℝ)^85 ≤ (2713810471021/12500000000000 : ℝ)^69 := by
    have hnat : (2894221147 : ℕ)^85*12500000000000^69 ≤ 2713810471021^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2894221147 10000000000 2713810471021 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485355367/10000000000 : ℝ)^85 ≤ (37243809739809/100000000000000 : ℝ)^69 := by
    have hnat : (4485355367 : ℕ)^85*100000000000000^69 ≤ 37243809739809^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485355367 10000000000 37243809739809 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1213401159/2500000000 : ℝ)^85 ≤ (8209141295661/20000000000000 : ℝ)^69 := by
    have hnat : (1213401159 : ℕ)^85*20000000000000^69 ≤ 8209141295661^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213401159 2500000000 8209141295661 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2894221147/10000000000 : ℝ), (4485355367/10000000000 : ℝ), (1213401159/2500000000 : ℝ)] ![(2713810471021/12500000000000 : ℝ), (37243809739809/100000000000000 : ℝ), (8209141295661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2894221147/10000000000 : ℝ)|^85 ≤ (2713810471021/12500000000000 : ℝ)^69
        have hw : |(2894221147/10000000000 : ℝ)|=(2894221147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485355367/10000000000 : ℝ)|^85 ≤ (37243809739809/100000000000000 : ℝ)^69
        have hw : |(4485355367/10000000000 : ℝ)|=(4485355367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1213401159/2500000000 : ℝ)|^85 ≤ (8209141295661/20000000000000 : ℝ)^69
        have hw : |(1213401159/2500000000 : ℝ)|=(1213401159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324083 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (83049/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1682709367/10000000000 : ℝ)*X 0 0+(4726226199/10000000000 : ℝ)*X 0 1+(1123551043/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((422556007/1250000000 : ℝ)*X 2 0+(6888933757/10000000000 : ℝ)*X 2 1+(-100506847/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3049055321/10000000000 : ℝ)*X 0 0+(263232663/1250000000 : ℝ)*X 0 1+(135988127/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2515016087/5000000000 : ℝ)*X 1 0+(118231/5000000000 : ℝ)*X 1 1+(1586492119/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((125694063/1250000000 : ℝ)*X 2 0+(3400049/3906250 : ℝ)*X 2 1+(-1518990653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2107613827/10000000000 : ℝ)*X 0 0+(3322356789/5000000000 : ℝ)*X 0 1+(646401773/2000000000 : ℝ)*X 0 2+(2107613827/10000000000 : ℝ)*X 1 0+(3322356789/5000000000 : ℝ)*X 1 1+(646401773/2000000000 : ℝ)*X 1 2+(2107613827/10000000000 : ℝ)*X 2 0+(3322356789/5000000000 : ℝ)*X 2 1+(646401773/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-354079451/10000000000 : ℝ)*X 0 0+(51945023/250000000 : ℝ)*X 0 1+(8674793791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((9333372799/10000000000 : ℝ)*X 1 0+(-2410823/10000000000 : ℝ)*X 1 1+(40804331/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1167921129/2500000000 : ℝ)*X 2 0+(6373527581/10000000000 : ℝ)*X 2 1+(-161674233/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((560322623/2500000000 : ℝ)*X 0 0+(129539959/500000000 : ℝ)*X 0 1+(282712767/400000000 : ℝ)*X 0 2+(560322623/2500000000 : ℝ)*X 1 0+(129539959/500000000 : ℝ)*X 1 1+(282712767/400000000 : ℝ)*X 1 2+(560322623/2500000000 : ℝ)*X 2 0+(129539959/500000000 : ℝ)*X 2 1+(282712767/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1317664893/10000000000 : ℝ)*X 0 0+(405937047/625000000 : ℝ)*X 0 1+(406573439/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8713603127/10000000000 : ℝ)*X 1 0+(-2423/5000000000 : ℝ)*X 1 1+(276674451/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((48345627/500000000 : ℝ)*X 2 0+(2086832943/2500000000 : ℝ)*X 2 1+(-1032630353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((3237871759/5000000000 : ℝ)*X 0 0+(155140123/500000000 : ℝ)*X 0 1+(615705369/2500000000 : ℝ)*X 0 2+(3237871759/5000000000 : ℝ)*X 1 0+(155140123/500000000 : ℝ)*X 1 1+(615705369/2500000000 : ℝ)*X 1 2+(3237871759/5000000000 : ℝ)*X 2 0+(155140123/500000000 : ℝ)*X 2 1+(615705369/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((59467/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(59467/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29219941945092733274829/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57962593629/50000000000 : ℝ)*(base7) + (9550171/500000000000 : ℝ)*(base23) + (261739550047/1000000000000 : ℝ)*(base49) + (6116943/1000000000000 : ℝ)*(base53) + (66936223937/1000000000000 : ℝ)*(base60) + (795010783217/500000000000 : ℝ)*(major_s0_0) + (795010783217/500000000000 : ℝ)*(major_s0_1) + (397503862373/250000000000 : ℝ)*(major_s0_2) + (6790879/500000000000 : ℝ)*(sp_s0_0) + (1736287220311/1000000000000 : ℝ)*(sp_s0_7) + (217038840011/125000000000 : ℝ)*(sp_s0_8) + (1736297736689/1000000000000 : ℝ)*(sp_s0_9) + (980571440323/500000000000 : ℝ)*(sp_s0_13) + (9918019/1000000000000 : ℝ)*(sp_s0_14) + (400945504033/500000000000 : ℝ)*(f.failure) + (1736316837031/1000000000000 : ℝ)*(f.sum) + (956015743276847/5000000000000000000000000000 : ℝ)*base62 + (196670759513537/2500000000000000000000000000 : ℝ)*base64 + (458203228929821/500000000000000000000000000 : ℝ)*base67 + (4010082877151/250000000000000000000000000 : ℝ)*base68 + (19354870230799/78125000000000000000000000 : ℝ)*base71 + (4183073195733827/5000000000000000000000000000 : ℝ)*base73 + (3229965283733827/5000000000000000000000000000 : ℝ)*base74 + (47653733479821/500000000000000000000000000 : ℝ)*base77 + (35392792967963/5000000000000000000000000000 : ℝ)*base78 + (5157/12500000000000000 : ℝ)*base86 + (5157/12500000000000000 : ℝ)*base88 + (17657/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((5683/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5683/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13998763361498081502093/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92633983401/125000000000 : ℝ)*(base7) + (23032723/1000000000000 : ℝ)*(base33) + (405936608761/1000000000000 : ℝ)*(base40) + (182361040493/1000000000000 : ℝ)*(base49) + (95030496523/250000000000 : ℝ)*(base60) + (1622827704353/1000000000000 : ℝ)*(major_s0_0) + (405712684269/250000000000 : ℝ)*(major_s0_1) + (405712684269/250000000000 : ℝ)*(major_s0_2) + (25466549/1000000000000 : ℝ)*(sp_s0_2) + (504236827131/250000000000 : ℝ)*(sp_s0_14) + (2016845258551/1000000000000 : ℝ)*(sp_s0_15) + (2016898809251/1000000000000 : ℝ)*(sp_s0_16) + (779759758289/500000000000 : ℝ)*(sp_s0_20) + (79017249/1000000000000 : ℝ)*(sp_s0_22) + (81844764937/100000000000 : ℝ)*(f.failure) + (504236827131/250000000000 : ℝ)*(f.sum) + (177064693148931/2500000000000000000000000000 : ℝ)*base63 + (1272270243333961/2500000000000000000000000000 : ℝ)*base64 + (142102391568503/250000000000000000000000000 : ℝ)*base66 + (112114843081497/250000000000000000000000000 : ℝ)*base69 + (87876562974977/5000000000000000000000000000 : ℝ)*base70 + (3009860972658157/10000000000000000000000000000 : ℝ)*base72 + (154280054333961/2500000000000000000000000000 : ℝ)*base75 + (188334717638589/1000000000000000000000000000 : ℝ)*base77 + (1888762437398277/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (2027/2500000000000000 : ℝ)*base87 + (2027/2500000000000000 : ℝ)*base89 + (2027/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64441/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64441/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3018578183297380871139/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301485229157/250000000000 : ℝ)*(base7) + (3910459/1000000000000 : ℝ)*(base11) + (249176494421/1000000000000 : ℝ)*(base40) + (38433/500000000000 : ℝ)*(base50) + (163868449887/100000000000 : ℝ)*(major_s0_0) + (163868449887/100000000000 : ℝ)*(major_s0_1) + (163868449887/100000000000 : ℝ)*(major_s0_2) + (2113091/200000000000 : ℝ)*(sp_s0_2) + (36261583/1000000000000 : ℝ)*(sp_s0_9) + (201627/200000000000 : ℝ)*(sp_s0_15) + (1783248782031/1000000000000 : ℝ)*(sp_s0_21) + (891625842177/500000000000 : ℝ)*(sp_s0_22) + (1783205865451/1000000000000 : ℝ)*(sp_s0_23) + (2032373961589/1000000000000 : ℝ)*(sp_s0_27) + (826433044961/1000000000000 : ℝ)*(f.failure) + (1783252692489/1000000000000 : ℝ)*(f.sum) + (262399700426287/1000000000000000000000000000 : ℝ)*base62 + (557688761408403/1000000000000000000000000000 : ℝ)*base64 + (46825754013469/100000000000000000000000000 : ℝ)*base66 + (21906311276531/100000000000000000000000000 : ℝ)*base69 + (435016766043093/1000000000000000000000000000 : ℝ)*base70 + (378101212191597/1000000000000000000000000000 : ℝ)*base73 + (236320559191597/1000000000000000000000000000 : ℝ)*base74 + (19201980143469/100000000000000000000000000 : ℝ)*base76 + (67880959156907/1000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (11731/25000000000000000 : ℝ)*base87 + (11731/25000000000000000 : ℝ)*base89 + (11731/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (59467/100000 : ℝ) ^ (21/4 : ℝ) ≤ (6530540932925226573/100000000000000000000 : ℝ) := by
    have hpowers : (59467/100000 : ℝ)^21 ≤ (6530540932925226573/100000000000000000000 : ℝ)^4 := by
      have hnat : (59467 : ℕ)^21*100000000000000000000^4 ≤ 6530540932925226573^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59467 100000 6530540932925226573 100000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59467/100000 : ℝ)) (X := (6530540932925226573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (106530540932925226573/100000000000000000000 : ℝ) ≤ (5060613531188371/5000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (106530540932925226573/100000000000000000000 : ℝ)^4 ≤ (5060613531188371/5000000000000000 : ℝ)^21 := by
      have hnat : (106530540932925226573 : ℕ)^4*5000000000000000^21 ≤ 5060613531188371^21*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106530540932925226573 100000000000000000000 5060613531188371 5000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060613531188371/5000000000000000 : ℝ)) (X := (106530540932925226573/100000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (56530540932925226573/50000000000000000000 : ℝ) ≤ (639786247595213/625000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (56530540932925226573/50000000000000000000 : ℝ)^4 ≤ (639786247595213/625000000000000 : ℝ)^21 := by
      have hnat : (56530540932925226573 : ℕ)^4*625000000000000^21 ≤ 639786247595213^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56530540932925226573 50000000000000000000 639786247595213 625000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (639786247595213/625000000000000 : ℝ)) (X := (56530540932925226573/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(60613531188371/2973350000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(57676449573333/2973350000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (59467/100000 : ℝ)) (alpha := (60613531188371/2973350000000000 : ℝ)) (beta := (57676449573333/2973350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (59467/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(60613531188371/2973350000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(57676449573333/2973350000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5683/10000 : ℝ) ^ (21/4 : ℝ) ≤ (1286686377257228743/25000000000000000000 : ℝ) := by
    have hpowers : (5683/10000 : ℝ)^21 ≤ (1286686377257228743/25000000000000000000 : ℝ)^4 := by
      have hnat : (5683 : ℕ)^21*25000000000000000000^4 ≤ 1286686377257228743^4*10000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5683 10000 1286686377257228743 25000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5683/10000 : ℝ)) (X := (1286686377257228743/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (26286686377257228743/25000000000000000000 : ℝ) ≤ (5048026103054227/5000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (26286686377257228743/25000000000000000000 : ℝ)^4 ≤ (5048026103054227/5000000000000000 : ℝ)^21 := by
      have hnat : (26286686377257228743 : ℕ)^4*5000000000000000^21 ≤ 5048026103054227^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26286686377257228743 25000000000000000000 5048026103054227 5000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048026103054227/5000000000000000 : ℝ)) (X := (26286686377257228743/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (13786686377257228743/12500000000000000000 : ℝ) ≤ (10188370734017749/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (13786686377257228743/12500000000000000000 : ℝ)^4 ≤ (10188370734017749/10000000000000000 : ℝ)^21 := by
      have hnat : (13786686377257228743 : ℕ)^4*10000000000000000^21 ≤ 10188370734017749^21*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13786686377257228743 12500000000000000000 10188370734017749 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10188370734017749/10000000000000000 : ℝ)) (X := (13786686377257228743/12500000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(48026103054227/2841500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(18463705581859/1136600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (5683/10000 : ℝ)) (alpha := (48026103054227/2841500000000000 : ℝ)) (beta := (18463705581859/1136600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (5683/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(48026103054227/2841500000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(18463705581859/1136600000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (64441/100000 : ℝ) ^ (21/4 : ℝ) ≤ (9956390548387694537/100000000000000000000 : ℝ) := by
    have hpowers : (64441/100000 : ℝ)^21 ≤ (9956390548387694537/100000000000000000000 : ℝ)^4 := by
      have hnat : (64441 : ℕ)^21*100000000000000000000^4 ≤ 9956390548387694537^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64441 100000 9956390548387694537 100000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64441/100000 : ℝ)) (X := (9956390548387694537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (109956390548387694537/100000000000000000000 : ℝ) ≤ (1018243201413531/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (109956390548387694537/100000000000000000000 : ℝ)^4 ≤ (1018243201413531/1000000000000000 : ℝ)^21 := by
      have hnat : (109956390548387694537 : ℕ)^4*1000000000000000^21 ≤ 1018243201413531^21*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109956390548387694537 100000000000000000000 1018243201413531 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1018243201413531/1000000000000000 : ℝ)) (X := (109956390548387694537/100000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (59956390548387694537/50000000000000000000 : ℝ) ≤ (2070389187934887/2000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (59956390548387694537/50000000000000000000 : ℝ)^4 ≤ (2070389187934887/2000000000000000 : ℝ)^21 := by
      have hnat : (59956390548387694537 : ℕ)^4*2000000000000000^21 ≤ 2070389187934887^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59956390548387694537 50000000000000000000 2070389187934887 2000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2070389187934887/2000000000000000 : ℝ)) (X := (59956390548387694537/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(18243201413531/644410000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1356111404313/51552800000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (64441/100000 : ℝ)) (alpha := (18243201413531/644410000000000 : ℝ)) (beta := (1356111404313/51552800000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (64441/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(18243201413531/644410000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1356111404313/51552800000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2311887053/10000000000 : ℝ)*X 0 0+(4679663447/10000000000 : ℝ)*X 0 1+(2581712613/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3285690073/5000000000 : ℝ)*X 1 0+(-189287003/2000000000 : ℝ)*X 1 1+(4255216749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1757638973/5000000000 : ℝ)*X 2 0+(1558955019/2500000000 : ℝ)*X 2 1+(-231908217/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2894221147/10000000000 : ℝ)*X 0 0+(4485355367/10000000000 : ℝ)*X 0 1+(1213401159/2500000000 : ℝ)*X 0 2+(2894221147/10000000000 : ℝ)*X 1 0+(4485355367/10000000000 : ℝ)*X 1 1+(1213401159/2500000000 : ℝ)*X 1 2+(2894221147/10000000000 : ℝ)*X 2 0+(4485355367/10000000000 : ℝ)*X 2 1+(1213401159/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324083_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-968595553186621869563702061552631533/108889489389005000000000000000000000 : ℝ) := by norm_num
    linear_combination (10577/200000000000 : ℝ)*(base7) + (24781/1000000000000 : ℝ)*(base8) + (5769/50000000000 : ℝ)*(base13) + (385989/1000000000000 : ℝ)*(base15) + (620429/1000000000000 : ℝ)*(base23) + (68559996423/250000000000 : ℝ)*(base40) + (38681390329/62500000000 : ℝ)*(base49) + (198909760679/1000000000000 : ℝ)*(base60) + (49571/25000 : ℝ)*(major_s1_0) + (49571/25000 : ℝ)*(major_s1_1) + (49571/25000 : ℝ)*(major_s1_2) + (593014381381/200000000000 : ℝ)*(sp_s1_0) + (1482535830539/500000000000 : ℝ)*(sp_s1_1) + (1482535713319/500000000000 : ℝ)*(sp_s1_2) + (200000010577/200000000000 : ℝ)*(sp_s1_6) + (2965072047067/1000000000000 : ℝ)*(f.sum) + (302666402372564039/366218203000000000000000000000 : ℝ)*base62 + (2527244865053/64441000000000000000000000 : ℝ)*base64 + (1790464930363/5683000000000000000000000 : ℝ)*base67 + (126423137681003/644410000000000000000000000 : ℝ)*base68 + (135354577669652247/306569035760000000000000000000 : ℝ)*base70 + (106244435920153/297335000000000000000000000 : ℝ)*base73 + (30730517826169/56830000000000000000000000 : ℝ)*base74 + (213509019285161/594670000000000000000000000 : ℝ)*base76 + (1610077189892107/4224387012500000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c324084_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4057422801/10000000000 : ℝ)*x 0 + (-4819394949/10000000000 : ℝ)*x 1 + (678314053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4057422801/10000000000 : ℝ)^85 ≤ (6583240830899/20000000000000 : ℝ)^69 := by
    have hnat : (4057422801 : ℕ)^85*20000000000000^69 ≤ 6583240830899^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4057422801 10000000000 6583240830899 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4819394949/10000000000 : ℝ)^85 ≤ (203448054493/500000000000 : ℝ)^69 := by
    have hnat : (4819394949 : ℕ)^85*500000000000^69 ≤ 203448054493^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819394949 10000000000 203448054493 500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678314053/2000000000 : ℝ)^85 ≤ (1649636558349/6250000000000 : ℝ)^69 := by
    have hnat : (678314053 : ℕ)^85*6250000000000^69 ≤ 1649636558349^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678314053 2000000000 1649636558349 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4057422801/10000000000 : ℝ), (-4819394949/10000000000 : ℝ), (678314053/2000000000 : ℝ)] ![(6583240830899/20000000000000 : ℝ), (203448054493/500000000000 : ℝ), (1649636558349/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4057422801/10000000000 : ℝ)|^85 ≤ (6583240830899/20000000000000 : ℝ)^69
        have hw : |(-4057422801/10000000000 : ℝ)|=(4057422801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4819394949/10000000000 : ℝ)|^85 ≤ (203448054493/500000000000 : ℝ)^69
        have hw : |(-4819394949/10000000000 : ℝ)|=(4819394949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678314053/2000000000 : ℝ)|^85 ≤ (1649636558349/6250000000000 : ℝ)^69
        have hw : |(678314053/2000000000 : ℝ)|=(678314053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324084_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (678314053/2000000000 : ℝ)*x 0 + (4057422801/10000000000 : ℝ)*x 1 + (4819394949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (678314053/2000000000 : ℝ)^85 ≤ (1649636558349/6250000000000 : ℝ)^69 := by
    have hnat : (678314053 : ℕ)^85*6250000000000^69 ≤ 1649636558349^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678314053 2000000000 1649636558349 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4057422801/10000000000 : ℝ)^85 ≤ (6583240830899/20000000000000 : ℝ)^69 := by
    have hnat : (4057422801 : ℕ)^85*20000000000000^69 ≤ 6583240830899^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4057422801 10000000000 6583240830899 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4819394949/10000000000 : ℝ)^85 ≤ (203448054493/500000000000 : ℝ)^69 := by
    have hnat : (4819394949 : ℕ)^85*500000000000^69 ≤ 203448054493^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819394949 10000000000 203448054493 500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(678314053/2000000000 : ℝ), (4057422801/10000000000 : ℝ), (4819394949/10000000000 : ℝ)] ![(1649636558349/6250000000000 : ℝ), (6583240830899/20000000000000 : ℝ), (203448054493/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(678314053/2000000000 : ℝ)|^85 ≤ (1649636558349/6250000000000 : ℝ)^69
        have hw : |(678314053/2000000000 : ℝ)|=(678314053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4057422801/10000000000 : ℝ)|^85 ≤ (6583240830899/20000000000000 : ℝ)^69
        have hw : |(4057422801/10000000000 : ℝ)|=(4057422801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4819394949/10000000000 : ℝ)|^85 ≤ (203448054493/500000000000 : ℝ)^69
        have hw : |(4819394949/10000000000 : ℝ)|=(4819394949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324084_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4819394949/10000000000 : ℝ)*x 0 + (-678314053/2000000000 : ℝ)*x 1 + (-4057422801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4819394949/10000000000 : ℝ)^85 ≤ (203448054493/500000000000 : ℝ)^69 := by
    have hnat : (4819394949 : ℕ)^85*500000000000^69 ≤ 203448054493^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819394949 10000000000 203448054493 500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678314053/2000000000 : ℝ)^85 ≤ (1649636558349/6250000000000 : ℝ)^69 := by
    have hnat : (678314053 : ℕ)^85*6250000000000^69 ≤ 1649636558349^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678314053 2000000000 1649636558349 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4057422801/10000000000 : ℝ)^85 ≤ (6583240830899/20000000000000 : ℝ)^69 := by
    have hnat : (4057422801 : ℕ)^85*20000000000000^69 ≤ 6583240830899^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4057422801 10000000000 6583240830899 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4819394949/10000000000 : ℝ), (-678314053/2000000000 : ℝ), (-4057422801/10000000000 : ℝ)] ![(203448054493/500000000000 : ℝ), (1649636558349/6250000000000 : ℝ), (6583240830899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4819394949/10000000000 : ℝ)|^85 ≤ (203448054493/500000000000 : ℝ)^69
        have hw : |(4819394949/10000000000 : ℝ)|=(4819394949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-678314053/2000000000 : ℝ)|^85 ≤ (1649636558349/6250000000000 : ℝ)^69
        have hw : |(-678314053/2000000000 : ℝ)|=(678314053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4057422801/10000000000 : ℝ)|^85 ≤ (6583240830899/20000000000000 : ℝ)^69
        have hw : |(-4057422801/10000000000 : ℝ)|=(4057422801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324084_s0_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4099112191/10000000000 : ℝ)*x 0 + (-4099112191/10000000000 : ℝ)*x 1 + (4099112191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4099112191/10000000000 : ℝ)^85 ≤ (8333333332073/25000000000000 : ℝ)^69 := by
    have hnat : (4099112191 : ℕ)^85*25000000000000^69 ≤ 8333333332073^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4099112191 10000000000 8333333332073 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4099112191/10000000000 : ℝ)^85 ≤ (8333333332073/25000000000000 : ℝ)^69 := by
    have hnat : (4099112191 : ℕ)^85*25000000000000^69 ≤ 8333333332073^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4099112191 10000000000 8333333332073 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4099112191/10000000000 : ℝ)^85 ≤ (8333333332073/25000000000000 : ℝ)^69 := by
    have hnat : (4099112191 : ℕ)^85*25000000000000^69 ≤ 8333333332073^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4099112191 10000000000 8333333332073 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4099112191/10000000000 : ℝ), (-4099112191/10000000000 : ℝ), (4099112191/10000000000 : ℝ)] ![(8333333332073/25000000000000 : ℝ), (8333333332073/25000000000000 : ℝ), (8333333332073/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4099112191/10000000000 : ℝ)|^85 ≤ (8333333332073/25000000000000 : ℝ)^69
        have hw : |(4099112191/10000000000 : ℝ)|=(4099112191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4099112191/10000000000 : ℝ)|^85 ≤ (8333333332073/25000000000000 : ℝ)^69
        have hw : |(-4099112191/10000000000 : ℝ)|=(4099112191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4099112191/10000000000 : ℝ)|^85 ≤ (8333333332073/25000000000000 : ℝ)^69
        have hw : |(4099112191/10000000000 : ℝ)|=(4099112191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324084 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base6 : ((-1 : ℝ)*T) ≤ (-1 : ℝ) := by
    linarith only [f.Tone]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-4057422801/10000000000 : ℝ)*X 0 0+(-4819394949/10000000000 : ℝ)*X 0 1+(678314053/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324084_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((678314053/2000000000 : ℝ)*X 1 0+(4057422801/10000000000 : ℝ)*X 1 1+(4819394949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324084_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4819394949/10000000000 : ℝ)*X 2 0+(-678314053/2000000000 : ℝ)*X 2 1+(-4057422801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324084_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((4099112191/10000000000 : ℝ)*X 0 0+(-4099112191/10000000000 : ℝ)*X 0 1+(4099112191/10000000000 : ℝ)*X 0 2+(4099112191/10000000000 : ℝ)*X 1 0+(-4099112191/10000000000 : ℝ)*X 1 1+(4099112191/10000000000 : ℝ)*X 1 2+(4099112191/10000000000 : ℝ)*X 2 0+(-4099112191/10000000000 : ℝ)*X 2 1+(4099112191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324084_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-86973131151596560423423/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (499999993213/500000000000 : ℝ)*(base6) + (606677383311/1000000000000 : ℝ)*(base40) + (606677383311/1000000000000 : ℝ)*(base50) + (606677383311/1000000000000 : ℝ)*(base60) + (49571/25000 : ℝ)*(major_s0_0) + (49571/25000 : ℝ)*(major_s0_1) + (49571/25000 : ℝ)*(major_s0_2) + (129297508021/40000000000 : ℝ)*(sp_s0_0) + (129297508021/40000000000 : ℝ)*(sp_s0_1) + (129297508021/40000000000 : ℝ)*(sp_s0_2) + (6787/500000000000 : ℝ)*(sp_s0_6) + (129297508021/40000000000 : ℝ)*(f.sum) + (7710979269/10000000000000000000000 : ℝ)*base62 + (1927928819/10000000000000000000000 : ℝ)*base65 + (2201138959/10000000000000000000000 : ℝ)*base66 + (2201138959/10000000000000000000000 : ℝ)*base68 + (7710979269/10000000000000000000000 : ℝ)*base71 + (1927928819/10000000000000000000000 : ℝ)*base72 + (1927928819/10000000000000000000000 : ℝ)*base74 + (2201138959/10000000000000000000000 : ℝ)*base77 + (7710979269/10000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p024_b043 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 83 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=83 ∨ c=84 := by omega
  rcases hc with rfl|rfl
  · exact collision_c324083 p hpa (by linarith only [hpb]) X hX
  · exact collision_c324084 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 83 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b043 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
