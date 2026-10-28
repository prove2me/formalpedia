-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b012
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:54:08.78779+00:00
-- url     : https://prove2.me/submissions/6bc3414c-1089-4229-b1e2-4f76df3a8672

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
theorem collision_support_c303025_s0_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1380180279/2500000000 : ℝ)*x 0 + (1603448311/5000000000 : ℝ)*x 1 + (64837171/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380180279/2500000000 : ℝ)^135 ≤ (2295139944031/5000000000000 : ℝ)^103 := by
    have hnat : (1380180279 : ℕ)^135*5000000000000^103 ≤ 2295139944031^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380180279 2500000000 2295139944031 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1603448311/5000000000 : ℝ)^135 ≤ (1126174350563/5000000000000 : ℝ)^103 := by
    have hnat : (1603448311 : ℕ)^135*5000000000000^103 ≤ 1126174350563^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1603448311 5000000000 1126174350563 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64837171/156250000 : ℝ)^135 ≤ (1973357130993/6250000000000 : ℝ)^103 := by
    have hnat : (64837171 : ℕ)^135*6250000000000^103 ≤ 1973357130993^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64837171 156250000 1973357130993 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1380180279/2500000000 : ℝ), (1603448311/5000000000 : ℝ), (64837171/156250000 : ℝ)] ![(2295139944031/5000000000000 : ℝ), (1126174350563/5000000000000 : ℝ), (1973357130993/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1380180279/2500000000 : ℝ)|^135 ≤ (2295139944031/5000000000000 : ℝ)^103
        have hw : |(-1380180279/2500000000 : ℝ)|=(1380180279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1603448311/5000000000 : ℝ)|^135 ≤ (1126174350563/5000000000000 : ℝ)^103
        have hw : |(1603448311/5000000000 : ℝ)|=(1603448311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64837171/156250000 : ℝ)|^135 ≤ (1973357130993/6250000000000 : ℝ)^103
        have hw : |(64837171/156250000 : ℝ)|=(64837171/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (469321111/1000000000 : ℝ)*x 0 + (-272620959/1000000000 : ℝ)*x 1 + (5409284241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469321111/1000000000 : ℝ)^135 ≤ (5936391409/16000000000 : ℝ)^103 := by
    have hnat : (469321111 : ℕ)^135*16000000000^103 ≤ 5936391409^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469321111 1000000000 5936391409 16000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272620959/1000000000 : ℝ)^135 ≤ (18205348856529/100000000000000 : ℝ)^103 := by
    have hnat : (272620959 : ℕ)^135*100000000000000^103 ≤ 18205348856529^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272620959 1000000000 18205348856529 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409284241/10000000000 : ℝ)^135 ≤ (44692204822173/100000000000000 : ℝ)^103 := by
    have hnat : (5409284241 : ℕ)^135*100000000000000^103 ≤ 44692204822173^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409284241 10000000000 44692204822173 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(469321111/1000000000 : ℝ), (-272620959/1000000000 : ℝ), (5409284241/10000000000 : ℝ)] ![(5936391409/16000000000 : ℝ), (18205348856529/100000000000000 : ℝ), (44692204822173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(469321111/1000000000 : ℝ)|^135 ≤ (5936391409/16000000000 : ℝ)^103
        have hw : |(469321111/1000000000 : ℝ)|=(469321111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-272620959/1000000000 : ℝ)|^135 ≤ (18205348856529/100000000000000 : ℝ)^103
        have hw : |(-272620959/1000000000 : ℝ)|=(272620959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409284241/10000000000 : ℝ)|^135 ≤ (44692204822173/100000000000000 : ℝ)^103
        have hw : |(5409284241/10000000000 : ℝ)|=(5409284241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1736469179/5000000000 : ℝ)*x 0 + (6654143437/10000000000 : ℝ)*x 1 + (-1256661087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1736469179/5000000000 : ℝ)^135 ≤ (1562719523513/6250000000000 : ℝ)^103 := by
    have hnat : (1736469179 : ℕ)^135*6250000000000^103 ≤ 1562719523513^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736469179 5000000000 1562719523513 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6654143437/10000000000 : ℝ)^135 ≤ (11726286327901/20000000000000 : ℝ)^103 := by
    have hnat : (6654143437 : ℕ)^135*20000000000000^103 ≤ 11726286327901^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6654143437 10000000000 11726286327901 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1256661087/5000000000 : ℝ)^135 ≤ (409126399279/2500000000000 : ℝ)^103 := by
    have hnat : (1256661087 : ℕ)^135*2500000000000^103 ≤ 409126399279^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256661087 5000000000 409126399279 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1736469179/5000000000 : ℝ), (6654143437/10000000000 : ℝ), (-1256661087/5000000000 : ℝ)] ![(1562719523513/6250000000000 : ℝ), (11726286327901/20000000000000 : ℝ), (409126399279/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1736469179/5000000000 : ℝ)|^135 ≤ (1562719523513/6250000000000 : ℝ)^103
        have hw : |(1736469179/5000000000 : ℝ)|=(1736469179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6654143437/10000000000 : ℝ)|^135 ≤ (11726286327901/20000000000000 : ℝ)^103
        have hw : |(6654143437/10000000000 : ℝ)|=(6654143437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1256661087/5000000000 : ℝ)|^135 ≤ (409126399279/2500000000000 : ℝ)^103
        have hw : |(-1256661087/5000000000 : ℝ)|=(1256661087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-231260653/400000000 : ℝ)*x 0 + (2539435499/10000000000 : ℝ)*x 1 + (4454246191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (231260653/400000000 : ℝ)^135 ≤ (24382766846837/50000000000000 : ℝ)^103 := by
    have hnat : (231260653 : ℕ)^135*50000000000000^103 ≤ 24382766846837^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231260653 400000000 24382766846837 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539435499/10000000000 : ℝ)^135 ≤ (8294136355747/50000000000000 : ℝ)^103 := by
    have hnat : (2539435499 : ℕ)^135*50000000000000^103 ≤ 8294136355747^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539435499 10000000000 8294136355747 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4454246191/10000000000 : ℝ)^135 ≤ (34646193572509/100000000000000 : ℝ)^103 := by
    have hnat : (4454246191 : ℕ)^135*100000000000000^103 ≤ 34646193572509^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4454246191 10000000000 34646193572509 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-231260653/400000000 : ℝ), (2539435499/10000000000 : ℝ), (4454246191/10000000000 : ℝ)] ![(24382766846837/50000000000000 : ℝ), (8294136355747/50000000000000 : ℝ), (34646193572509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-231260653/400000000 : ℝ)|^135 ≤ (24382766846837/50000000000000 : ℝ)^103
        have hw : |(-231260653/400000000 : ℝ)|=(231260653/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539435499/10000000000 : ℝ)|^135 ≤ (8294136355747/50000000000000 : ℝ)^103
        have hw : |(2539435499/10000000000 : ℝ)|=(2539435499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4454246191/10000000000 : ℝ)|^135 ≤ (34646193572509/100000000000000 : ℝ)^103
        have hw : |(4454246191/10000000000 : ℝ)|=(4454246191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (554871739/1250000000 : ℝ)*x 0 + (-1949745931/10000000000 : ℝ)*x 1 + (622952581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (554871739/1250000000 : ℝ)^135 ≤ (17245289520803/50000000000000 : ℝ)^103 := by
    have hnat : (554871739 : ℕ)^135*50000000000000^103 ≤ 17245289520803^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554871739 1250000000 17245289520803 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1949745931/10000000000 : ℝ)^135 ≤ (586622443843/5000000000000 : ℝ)^103 := by
    have hnat : (1949745931 : ℕ)^135*5000000000000^103 ≤ 586622443843^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949745931 10000000000 586622443843 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (622952581/1000000000 : ℝ)^135 ≤ (2151078882863/4000000000000 : ℝ)^103 := by
    have hnat : (622952581 : ℕ)^135*4000000000000^103 ≤ 2151078882863^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622952581 1000000000 2151078882863 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(554871739/1250000000 : ℝ), (-1949745931/10000000000 : ℝ), (622952581/1000000000 : ℝ)] ![(17245289520803/50000000000000 : ℝ), (586622443843/5000000000000 : ℝ), (2151078882863/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(554871739/1250000000 : ℝ)|^135 ≤ (17245289520803/50000000000000 : ℝ)^103
        have hw : |(554871739/1250000000 : ℝ)|=(554871739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1949745931/10000000000 : ℝ)|^135 ≤ (586622443843/5000000000000 : ℝ)^103
        have hw : |(-1949745931/10000000000 : ℝ)|=(1949745931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(622952581/1000000000 : ℝ)|^135 ≤ (2151078882863/4000000000000 : ℝ)^103
        have hw : |(622952581/1000000000 : ℝ)|=(622952581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2783049329/10000000000 : ℝ)*x 0 + (7473493013/10000000000 : ℝ)*x 1 + (-2111649607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2783049329/10000000000 : ℝ)^135 ≤ (584513971013/3125000000000 : ℝ)^103 := by
    have hnat : (2783049329 : ℕ)^135*3125000000000^103 ≤ 584513971013^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783049329 10000000000 584513971013 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7473493013/10000000000 : ℝ)^135 ≤ (13654003186309/20000000000000 : ℝ)^103 := by
    have hnat : (7473493013 : ℕ)^135*20000000000000^103 ≤ 13654003186309^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7473493013 10000000000 13654003186309 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111649607/10000000000 : ℝ)^135 ≤ (6512768492939/50000000000000 : ℝ)^103 := by
    have hnat : (2111649607 : ℕ)^135*50000000000000^103 ≤ 6512768492939^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111649607 10000000000 6512768492939 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2783049329/10000000000 : ℝ), (7473493013/10000000000 : ℝ), (-2111649607/10000000000 : ℝ)] ![(584513971013/3125000000000 : ℝ), (13654003186309/20000000000000 : ℝ), (6512768492939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2783049329/10000000000 : ℝ)|^135 ≤ (584513971013/3125000000000 : ℝ)^103
        have hw : |(2783049329/10000000000 : ℝ)|=(2783049329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7473493013/10000000000 : ℝ)|^135 ≤ (13654003186309/20000000000000 : ℝ)^103
        have hw : |(7473493013/10000000000 : ℝ)|=(7473493013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111649607/10000000000 : ℝ)|^135 ≤ (6512768492939/50000000000000 : ℝ)^103
        have hw : |(-2111649607/10000000000 : ℝ)|=(2111649607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_12 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2255996613/10000000000 : ℝ)*x 0 + (6058166037/10000000000 : ℝ)*x 1 + (2192836963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2255996613/10000000000 : ℝ)^135 ≤ (7102379698957/50000000000000 : ℝ)^103 := by
    have hnat : (2255996613 : ℕ)^135*50000000000000^103 ≤ 7102379698957^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255996613 10000000000 7102379698957 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6058166037/10000000000 : ℝ)^135 ≤ (51846448420391/100000000000000 : ℝ)^103 := by
    have hnat : (6058166037 : ℕ)^135*100000000000000^103 ≤ 51846448420391^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6058166037 10000000000 51846448420391 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2192836963/5000000000 : ℝ)^135 ≤ (8487198043111/25000000000000 : ℝ)^103 := by
    have hnat : (2192836963 : ℕ)^135*25000000000000^103 ≤ 8487198043111^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192836963 5000000000 8487198043111 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2255996613/10000000000 : ℝ), (6058166037/10000000000 : ℝ), (2192836963/5000000000 : ℝ)] ![(7102379698957/50000000000000 : ℝ), (51846448420391/100000000000000 : ℝ), (8487198043111/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2255996613/10000000000 : ℝ)|^135 ≤ (7102379698957/50000000000000 : ℝ)^103
        have hw : |(2255996613/10000000000 : ℝ)|=(2255996613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6058166037/10000000000 : ℝ)|^135 ≤ (51846448420391/100000000000000 : ℝ)^103
        have hw : |(6058166037/10000000000 : ℝ)|=(6058166037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2192836963/5000000000 : ℝ)|^135 ≤ (8487198043111/25000000000000 : ℝ)^103
        have hw : |(2192836963/5000000000 : ℝ)|=(2192836963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5735618219/10000000000 : ℝ)*x 0 + (2318673217/10000000000 : ℝ)*x 1 + (2342482657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5735618219/10000000000 : ℝ)^135 ≤ (3016171655151/6250000000000 : ℝ)^103 := by
    have hnat : (5735618219 : ℕ)^135*6250000000000^103 ≤ 3016171655151^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5735618219 10000000000 3016171655151 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2318673217/10000000000 : ℝ)^135 ≤ (14724223941001/100000000000000 : ℝ)^103 := by
    have hnat : (2318673217 : ℕ)^135*100000000000000^103 ≤ 14724223941001^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2318673217 10000000000 14724223941001 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2342482657/5000000000 : ℝ)^135 ≤ (37017029566537/100000000000000 : ℝ)^103 := by
    have hnat : (2342482657 : ℕ)^135*100000000000000^103 ≤ 37017029566537^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2342482657 5000000000 37017029566537 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5735618219/10000000000 : ℝ), (2318673217/10000000000 : ℝ), (2342482657/5000000000 : ℝ)] ![(3016171655151/6250000000000 : ℝ), (14724223941001/100000000000000 : ℝ), (37017029566537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5735618219/10000000000 : ℝ)|^135 ≤ (3016171655151/6250000000000 : ℝ)^103
        have hw : |(-5735618219/10000000000 : ℝ)|=(5735618219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2318673217/10000000000 : ℝ)|^135 ≤ (14724223941001/100000000000000 : ℝ)^103
        have hw : |(2318673217/10000000000 : ℝ)|=(2318673217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2342482657/5000000000 : ℝ)|^135 ≤ (37017029566537/100000000000000 : ℝ)^103
        have hw : |(2342482657/5000000000 : ℝ)|=(2342482657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5509851201/10000000000 : ℝ)*x 0 + (-369224017/1250000000 : ℝ)*x 1 + (4390029241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5509851201/10000000000 : ℝ)^135 ≤ (22892188338387/50000000000000 : ℝ)^103 := by
    have hnat : (5509851201 : ℕ)^135*50000000000000^103 ≤ 22892188338387^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509851201 10000000000 22892188338387 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369224017/1250000000 : ℝ)^135 ≤ (10111318173099/50000000000000 : ℝ)^103 := by
    have hnat : (369224017 : ℕ)^135*50000000000000^103 ≤ 10111318173099^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369224017 1250000000 10111318173099 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4390029241/10000000000 : ℝ)^135 ≤ (1359719478517/4000000000000 : ℝ)^103 := by
    have hnat : (4390029241 : ℕ)^135*4000000000000^103 ≤ 1359719478517^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4390029241 10000000000 1359719478517 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5509851201/10000000000 : ℝ), (-369224017/1250000000 : ℝ), (4390029241/10000000000 : ℝ)] ![(22892188338387/50000000000000 : ℝ), (10111318173099/50000000000000 : ℝ), (1359719478517/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5509851201/10000000000 : ℝ)|^135 ≤ (22892188338387/50000000000000 : ℝ)^103
        have hw : |(5509851201/10000000000 : ℝ)|=(5509851201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-369224017/1250000000 : ℝ)|^135 ≤ (10111318173099/50000000000000 : ℝ)^103
        have hw : |(-369224017/1250000000 : ℝ)|=(369224017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4390029241/10000000000 : ℝ)|^135 ≤ (1359719478517/4000000000000 : ℝ)^103
        have hw : |(4390029241/10000000000 : ℝ)|=(4390029241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (627145249/2000000000 : ℝ)*x 0 + (140554467/200000000 : ℝ)*x 1 + (-2369230243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (627145249/2000000000 : ℝ)^135 ≤ (21870598612899/100000000000000 : ℝ)^103 := by
    have hnat : (627145249 : ℕ)^135*100000000000000^103 ≤ 21870598612899^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627145249 2000000000 21870598612899 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140554467/200000000 : ℝ)^135 ≤ (31491481942413/50000000000000 : ℝ)^103 := by
    have hnat : (140554467 : ℕ)^135*50000000000000^103 ≤ 31491481942413^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140554467 200000000 31491481942413 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2369230243/10000000000 : ℝ)^135 ≤ (15146437479613/100000000000000 : ℝ)^103 := by
    have hnat : (2369230243 : ℕ)^135*100000000000000^103 ≤ 15146437479613^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369230243 10000000000 15146437479613 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(627145249/2000000000 : ℝ), (140554467/200000000 : ℝ), (-2369230243/10000000000 : ℝ)] ![(21870598612899/100000000000000 : ℝ), (31491481942413/50000000000000 : ℝ), (15146437479613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(627145249/2000000000 : ℝ)|^135 ≤ (21870598612899/100000000000000 : ℝ)^103
        have hw : |(627145249/2000000000 : ℝ)|=(627145249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140554467/200000000 : ℝ)|^135 ≤ (31491481942413/50000000000000 : ℝ)^103
        have hw : |(140554467/200000000 : ℝ)|=(140554467/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2369230243/10000000000 : ℝ)|^135 ≤ (15146437479613/100000000000000 : ℝ)^103
        have hw : |(-2369230243/10000000000 : ℝ)|=(2369230243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_19 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (600401207/5000000000 : ℝ)*x 0 + (3986557703/10000000000 : ℝ)*x 1 + (3549709801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (600401207/5000000000 : ℝ)^135 ≤ (6215586742143/100000000000000 : ℝ)^103 := by
    have hnat : (600401207 : ℕ)^135*100000000000000^103 ≤ 6215586742143^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600401207 5000000000 6215586742143 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3986557703/10000000000 : ℝ)^135 ≤ (29957944601729/100000000000000 : ℝ)^103 := by
    have hnat : (3986557703 : ℕ)^135*100000000000000^103 ≤ 29957944601729^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3986557703 10000000000 29957944601729 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3549709801/5000000000 : ℝ)^135 ≤ (63826468648187/100000000000000 : ℝ)^103 := by
    have hnat : (3549709801 : ℕ)^135*100000000000000^103 ≤ 63826468648187^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3549709801 5000000000 63826468648187 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(600401207/5000000000 : ℝ), (3986557703/10000000000 : ℝ), (3549709801/5000000000 : ℝ)] ![(6215586742143/100000000000000 : ℝ), (29957944601729/100000000000000 : ℝ), (63826468648187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(600401207/5000000000 : ℝ)|^135 ≤ (6215586742143/100000000000000 : ℝ)^103
        have hw : |(600401207/5000000000 : ℝ)|=(600401207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3986557703/10000000000 : ℝ)|^135 ≤ (29957944601729/100000000000000 : ℝ)^103
        have hw : |(3986557703/10000000000 : ℝ)|=(3986557703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3549709801/5000000000 : ℝ)|^135 ≤ (63826468648187/100000000000000 : ℝ)^103
        have hw : |(3549709801/5000000000 : ℝ)|=(3549709801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-6260818653/10000000000 : ℝ)*x 0 + (1238606577/5000000000 : ℝ)*x 1 + (794328109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6260818653/10000000000 : ℝ)^135 ≤ (27065656487257/50000000000000 : ℝ)^103 := by
    have hnat : (6260818653 : ℕ)^135*50000000000000^103 ≤ 27065656487257^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6260818653 10000000000 27065656487257 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1238606577/5000000000 : ℝ)^135 ≤ (8028791118997/50000000000000 : ℝ)^103 := by
    have hnat : (1238606577 : ℕ)^135*50000000000000^103 ≤ 8028791118997^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238606577 5000000000 8028791118997 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (794328109/2000000000 : ℝ)^135 ≤ (29811104775087/100000000000000 : ℝ)^103 := by
    have hnat : (794328109 : ℕ)^135*100000000000000^103 ≤ 29811104775087^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794328109 2000000000 29811104775087 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6260818653/10000000000 : ℝ), (1238606577/5000000000 : ℝ), (794328109/2000000000 : ℝ)] ![(27065656487257/50000000000000 : ℝ), (8028791118997/50000000000000 : ℝ), (29811104775087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6260818653/10000000000 : ℝ)|^135 ≤ (27065656487257/50000000000000 : ℝ)^103
        have hw : |(-6260818653/10000000000 : ℝ)|=(6260818653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1238606577/5000000000 : ℝ)|^135 ≤ (8028791118997/50000000000000 : ℝ)^103
        have hw : |(1238606577/5000000000 : ℝ)|=(1238606577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(794328109/2000000000 : ℝ)|^135 ≤ (29811104775087/100000000000000 : ℝ)^103
        have hw : |(794328109/2000000000 : ℝ)|=(794328109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (792607087/2000000000 : ℝ)*x 0 + (-3630530749/10000000000 : ℝ)*x 1 + (5324150299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (792607087/2000000000 : ℝ)^135 ≤ (5945295325313/20000000000000 : ℝ)^103 := by
    have hnat : (792607087 : ℕ)^135*20000000000000^103 ≤ 5945295325313^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792607087 2000000000 5945295325313 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3630530749/10000000000 : ℝ)^135 ≤ (13250486113861/50000000000000 : ℝ)^103 := by
    have hnat : (3630530749 : ℕ)^135*50000000000000^103 ≤ 13250486113861^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3630530749 10000000000 13250486113861 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5324150299/10000000000 : ℝ)^135 ≤ (2735784445363/6250000000000 : ℝ)^103 := by
    have hnat : (5324150299 : ℕ)^135*6250000000000^103 ≤ 2735784445363^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5324150299 10000000000 2735784445363 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(792607087/2000000000 : ℝ), (-3630530749/10000000000 : ℝ), (5324150299/10000000000 : ℝ)] ![(5945295325313/20000000000000 : ℝ), (13250486113861/50000000000000 : ℝ), (2735784445363/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(792607087/2000000000 : ℝ)|^135 ≤ (5945295325313/20000000000000 : ℝ)^103
        have hw : |(792607087/2000000000 : ℝ)|=(792607087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3630530749/10000000000 : ℝ)|^135 ≤ (13250486113861/50000000000000 : ℝ)^103
        have hw : |(-3630530749/10000000000 : ℝ)|=(3630530749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5324150299/10000000000 : ℝ)|^135 ≤ (2735784445363/6250000000000 : ℝ)^103
        have hw : |(5324150299/10000000000 : ℝ)|=(5324150299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2055493467/5000000000 : ℝ)*x 0 + (6201829769/10000000000 : ℝ)*x 1 + (-1196551311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055493467/5000000000 : ℝ)^135 ≤ (31189399960411/100000000000000 : ℝ)^103 := by
    have hnat : (2055493467 : ℕ)^135*100000000000000^103 ≤ 31189399960411^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055493467 5000000000 31189399960411 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6201829769/10000000000 : ℝ)^135 ≤ (53463820031317/100000000000000 : ℝ)^103 := by
    have hnat : (6201829769 : ℕ)^135*100000000000000^103 ≤ 53463820031317^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6201829769 10000000000 53463820031317 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196551311/5000000000 : ℝ)^135 ≤ (15346780001853/100000000000000 : ℝ)^103 := by
    have hnat : (1196551311 : ℕ)^135*100000000000000^103 ≤ 15346780001853^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196551311 5000000000 15346780001853 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2055493467/5000000000 : ℝ), (6201829769/10000000000 : ℝ), (-1196551311/5000000000 : ℝ)] ![(31189399960411/100000000000000 : ℝ), (53463820031317/100000000000000 : ℝ), (15346780001853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2055493467/5000000000 : ℝ)|^135 ≤ (31189399960411/100000000000000 : ℝ)^103
        have hw : |(2055493467/5000000000 : ℝ)|=(2055493467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6201829769/10000000000 : ℝ)|^135 ≤ (53463820031317/100000000000000 : ℝ)^103
        have hw : |(6201829769/10000000000 : ℝ)|=(6201829769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1196551311/5000000000 : ℝ)|^135 ≤ (15346780001853/100000000000000 : ℝ)^103
        have hw : |(-1196551311/5000000000 : ℝ)|=(1196551311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s0_26 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1293904881/10000000000 : ℝ)*x 0 + (5361451259/10000000000 : ℝ)*x 1 + (1450008773/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293904881/10000000000 : ℝ)^135 ≤ (1370940208729/20000000000000 : ℝ)^103 := by
    have hnat : (1293904881 : ℕ)^135*20000000000000^103 ≤ 1370940208729^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293904881 10000000000 1370940208729 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5361451259/10000000000 : ℝ)^135 ≤ (1380466694689/3125000000000 : ℝ)^103 := by
    have hnat : (5361451259 : ℕ)^135*3125000000000^103 ≤ 1380466694689^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361451259 10000000000 1380466694689 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1450008773/2500000000 : ℝ)^135 ≤ (3060647794243/6250000000000 : ℝ)^103 := by
    have hnat : (1450008773 : ℕ)^135*6250000000000^103 ≤ 3060647794243^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1450008773 2500000000 3060647794243 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293904881/10000000000 : ℝ), (5361451259/10000000000 : ℝ), (1450008773/2500000000 : ℝ)] ![(1370940208729/20000000000000 : ℝ), (1380466694689/3125000000000 : ℝ), (3060647794243/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293904881/10000000000 : ℝ)|^135 ≤ (1370940208729/20000000000000 : ℝ)^103
        have hw : |(1293904881/10000000000 : ℝ)|=(1293904881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5361451259/10000000000 : ℝ)|^135 ≤ (1380466694689/3125000000000 : ℝ)^103
        have hw : |(5361451259/10000000000 : ℝ)|=(5361451259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1450008773/2500000000 : ℝ)|^135 ≤ (3060647794243/6250000000000 : ℝ)^103
        have hw : |(1450008773/2500000000 : ℝ)|=(1450008773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s1_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-243564371/500000000 : ℝ)*x 0 + (1010884997/2500000000 : ℝ)*x 1 + (4043615673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (243564371/500000000 : ℝ)^135 ≤ (19479196667847/50000000000000 : ℝ)^103 := by
    have hnat : (243564371 : ℕ)^135*50000000000000^103 ≤ 19479196667847^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243564371 500000000 19479196667847 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010884997/2500000000 : ℝ)^135 ≤ (1220817158179/4000000000000 : ℝ)^103 := by
    have hnat : (1010884997 : ℕ)^135*4000000000000^103 ≤ 1220817158179^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010884997 2500000000 1220817158179 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4043615673/10000000000 : ℝ)^135 ≤ (30521177703919/100000000000000 : ℝ)^103 := by
    have hnat : (4043615673 : ℕ)^135*100000000000000^103 ≤ 30521177703919^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043615673 10000000000 30521177703919 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-243564371/500000000 : ℝ), (1010884997/2500000000 : ℝ), (4043615673/10000000000 : ℝ)] ![(19479196667847/50000000000000 : ℝ), (1220817158179/4000000000000 : ℝ), (30521177703919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-243564371/500000000 : ℝ)|^135 ≤ (19479196667847/50000000000000 : ℝ)^103
        have hw : |(-243564371/500000000 : ℝ)|=(243564371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1010884997/2500000000 : ℝ)|^135 ≤ (1220817158179/4000000000000 : ℝ)^103
        have hw : |(1010884997/2500000000 : ℝ)|=(1010884997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4043615673/10000000000 : ℝ)|^135 ≤ (30521177703919/100000000000000 : ℝ)^103
        have hw : |(4043615673/10000000000 : ℝ)|=(4043615673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s1_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4187195061/10000000000 : ℝ)*x 0 + (-3475691169/10000000000 : ℝ)*x 1 + (5254274707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187195061/10000000000 : ℝ)^135 ≤ (7987345049117/25000000000000 : ℝ)^103 := by
    have hnat : (4187195061 : ℕ)^135*25000000000000^103 ≤ 7987345049117^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187195061 10000000000 7987345049117 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3475691169/10000000000 : ℝ)^135 ≤ (5005898369947/20000000000000 : ℝ)^103 := by
    have hnat : (3475691169 : ℕ)^135*20000000000000^103 ≤ 5005898369947^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3475691169 10000000000 5005898369947 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254274707/10000000000 : ℝ)^135 ≤ (860422558643/2000000000000 : ℝ)^103 := by
    have hnat : (5254274707 : ℕ)^135*2000000000000^103 ≤ 860422558643^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254274707 10000000000 860422558643 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187195061/10000000000 : ℝ), (-3475691169/10000000000 : ℝ), (5254274707/10000000000 : ℝ)] ![(7987345049117/25000000000000 : ℝ), (5005898369947/20000000000000 : ℝ), (860422558643/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187195061/10000000000 : ℝ)|^135 ≤ (7987345049117/25000000000000 : ℝ)^103
        have hw : |(4187195061/10000000000 : ℝ)|=(4187195061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3475691169/10000000000 : ℝ)|^135 ≤ (5005898369947/20000000000000 : ℝ)^103
        have hw : |(-3475691169/10000000000 : ℝ)|=(3475691169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254274707/10000000000 : ℝ)|^135 ≤ (860422558643/2000000000000 : ℝ)^103
        have hw : |(5254274707/10000000000 : ℝ)|=(5254274707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s1_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4187135143/10000000000 : ℝ)*x 0 + (328394817/625000000 : ℝ)*x 1 + (-434463311/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187135143/10000000000 : ℝ)^135 ≤ (15974390484211/50000000000000 : ℝ)^103 := by
    have hnat : (4187135143 : ℕ)^135*50000000000000^103 ≤ 15974390484211^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187135143 10000000000 15974390484211 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328394817/625000000 : ℝ)^135 ≤ (43021582578089/100000000000000 : ℝ)^103 := by
    have hnat : (328394817 : ℕ)^135*100000000000000^103 ≤ 43021582578089^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328394817 625000000 43021582578089 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434463311/1250000000 : ℝ)^135 ≤ (5005927287937/20000000000000 : ℝ)^103 := by
    have hnat : (434463311 : ℕ)^135*20000000000000^103 ≤ 5005927287937^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434463311 1250000000 5005927287937 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187135143/10000000000 : ℝ), (328394817/625000000 : ℝ), (-434463311/1250000000 : ℝ)] ![(15974390484211/50000000000000 : ℝ), (43021582578089/100000000000000 : ℝ), (5005927287937/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187135143/10000000000 : ℝ)|^135 ≤ (15974390484211/50000000000000 : ℝ)^103
        have hw : |(4187135143/10000000000 : ℝ)|=(4187135143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328394817/625000000 : ℝ)|^135 ≤ (43021582578089/100000000000000 : ℝ)^103
        have hw : |(328394817/625000000 : ℝ)|=(328394817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434463311/1250000000 : ℝ)|^135 ≤ (5005927287937/20000000000000 : ℝ)^103
        have hw : |(-434463311/1250000000 : ℝ)|=(434463311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303025_s1_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1845312113/5000000000 : ℝ)*x 0 + (4631259611/10000000000 : ℝ)*x 1 + (4631155999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1845312113/5000000000 : ℝ)^135 ≤ (13538687853051/50000000000000 : ℝ)^103 := by
    have hnat : (1845312113 : ℕ)^135*50000000000000^103 ≤ 13538687853051^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845312113 5000000000 13538687853051 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4631259611/10000000000 : ℝ)^135 ≤ (36461846723323/100000000000000 : ℝ)^103 := by
    have hnat : (4631259611 : ℕ)^135*100000000000000^103 ≤ 36461846723323^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4631259611 10000000000 36461846723323 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4631155999/10000000000 : ℝ)^135 ≤ (9115194389647/25000000000000 : ℝ)^103 := by
    have hnat : (4631155999 : ℕ)^135*25000000000000^103 ≤ 9115194389647^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4631155999 10000000000 9115194389647 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1845312113/5000000000 : ℝ), (4631259611/10000000000 : ℝ), (4631155999/10000000000 : ℝ)] ![(13538687853051/50000000000000 : ℝ), (36461846723323/100000000000000 : ℝ), (9115194389647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1845312113/5000000000 : ℝ)|^135 ≤ (13538687853051/50000000000000 : ℝ)^103
        have hw : |(1845312113/5000000000 : ℝ)|=(1845312113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4631259611/10000000000 : ℝ)|^135 ≤ (36461846723323/100000000000000 : ℝ)^103
        have hw : |(4631259611/10000000000 : ℝ)|=(4631259611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4631155999/10000000000 : ℝ)|^135 ≤ (9115194389647/25000000000000 : ℝ)^103
        have hw : |(4631155999/10000000000 : ℝ)|=(4631155999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303025 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1380180279/2500000000 : ℝ)*X 0 0+(1603448311/5000000000 : ℝ)*X 0 1+(64837171/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((469321111/1000000000 : ℝ)*X 1 0+(-272620959/1000000000 : ℝ)*X 1 1+(5409284241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1736469179/5000000000 : ℝ)*X 2 0+(6654143437/10000000000 : ℝ)*X 2 1+(-1256661087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-231260653/400000000 : ℝ)*X 0 0+(2539435499/10000000000 : ℝ)*X 0 1+(4454246191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((554871739/1250000000 : ℝ)*X 1 0+(-1949745931/10000000000 : ℝ)*X 1 1+(622952581/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2783049329/10000000000 : ℝ)*X 2 0+(7473493013/10000000000 : ℝ)*X 2 1+(-2111649607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((2255996613/10000000000 : ℝ)*X 0 0+(6058166037/10000000000 : ℝ)*X 0 1+(2192836963/5000000000 : ℝ)*X 0 2+(2255996613/10000000000 : ℝ)*X 1 0+(6058166037/10000000000 : ℝ)*X 1 1+(2192836963/5000000000 : ℝ)*X 1 2+(2255996613/10000000000 : ℝ)*X 2 0+(6058166037/10000000000 : ℝ)*X 2 1+(2192836963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-5735618219/10000000000 : ℝ)*X 0 0+(2318673217/10000000000 : ℝ)*X 0 1+(2342482657/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((5509851201/10000000000 : ℝ)*X 1 0+(-369224017/1250000000 : ℝ)*X 1 1+(4390029241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((627145249/2000000000 : ℝ)*X 2 0+(140554467/200000000 : ℝ)*X 2 1+(-2369230243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((600401207/5000000000 : ℝ)*X 0 0+(3986557703/10000000000 : ℝ)*X 0 1+(3549709801/5000000000 : ℝ)*X 0 2+(600401207/5000000000 : ℝ)*X 1 0+(3986557703/10000000000 : ℝ)*X 1 1+(3549709801/5000000000 : ℝ)*X 1 2+(600401207/5000000000 : ℝ)*X 2 0+(3986557703/10000000000 : ℝ)*X 2 1+(3549709801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-6260818653/10000000000 : ℝ)*X 0 0+(1238606577/5000000000 : ℝ)*X 0 1+(794328109/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((792607087/2000000000 : ℝ)*X 1 0+(-3630530749/10000000000 : ℝ)*X 1 1+(5324150299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2055493467/5000000000 : ℝ)*X 2 0+(6201829769/10000000000 : ℝ)*X 2 1+(-1196551311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_26 : ((1293904881/10000000000 : ℝ)*X 0 0+(5361451259/10000000000 : ℝ)*X 0 1+(1450008773/2500000000 : ℝ)*X 0 2+(1293904881/10000000000 : ℝ)*X 1 0+(5361451259/10000000000 : ℝ)*X 1 1+(1450008773/2500000000 : ℝ)*X 1 2+(1293904881/10000000000 : ℝ)*X 2 0+(5361451259/10000000000 : ℝ)*X 2 1+(1450008773/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s0_26 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((26329/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26329/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38151822813350877973137/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (548412887383/500000000000 : ℝ)*(base50) + (174444049499/250000000000 : ℝ)*(base59) + (288037139/3906250000 : ℝ)*(base60) + (4627305896759/1000000000000 : ℝ)*(major_s0_0) + (4627305896759/1000000000000 : ℝ)*(major_s0_1) + (4627305896759/1000000000000 : ℝ)*(major_s0_2) + (278104343/1000000000000 : ℝ)*(sp_s0_0) + (1289721/200000000000 : ℝ)*(sp_s0_1) + (1235510397647/200000000000 : ℝ)*(sp_s0_7) + (6178343179977/1000000000000 : ℝ)*(sp_s0_8) + (3089174814291/500000000000 : ℝ)*(sp_s0_9) + (3076229298057/1000000000000 : ℝ)*(sp_s0_12) + (103907201/200000000000 : ℝ)*(sp_s0_13) + (6944991/250000000000 : ℝ)*(sp_s0_26) + (3076257078021/1000000000000 : ℝ)*(f.failure) + (3089174814291/500000000000 : ℝ)*(f.sum) + (607756583709501/1000000000000000000000000000 : ℝ)*base63 + (1124061436405471/1250000000000000000000000000 : ℝ)*base64 + (1039042588344529/1250000000000000000000000000 : ℝ)*base66 + (438063920609501/2000000000000000000000000000 : ℝ)*base69 + (5079850660291273/10000000000000000000000000000 : ℝ)*base70 + (117441704344529/1250000000000000000000000000 : ℝ)*base72 + (938048060190499/2000000000000000000000000000 : ℝ)*base74 + (353905750609501/2000000000000000000000000000 : ℝ)*base76 + (186353823469529/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (941/5000000000000000 : ℝ)*base87 + (941/5000000000000000 : ℝ)*base89 + (941/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1989/12500 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1989/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38210184504420698628879/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223911228389/1000000000000 : ℝ)*(base40) + (44337594937/500000000000 : ℝ)*(base50) + (219570387727/250000000000 : ℝ)*(base59) + (7484949/1000000000000 : ℝ)*(base60) + (3434412917419/1000000000000 : ℝ)*(major_s0_0) + (3434412917419/1000000000000 : ℝ)*(major_s0_1) + (3434412917419/1000000000000 : ℝ)*(major_s0_2) + (52097979/200000000000 : ℝ)*(sp_s0_2) + (32396981/1000000000000 : ℝ)*(sp_s0_8) + (4585548509017/1000000000000 : ℝ)*(sp_s0_13) + (4585572735249/1000000000000 : ℝ)*(sp_s0_14) + (917068928467/200000000000 : ℝ)*(sp_s0_15) + (2283215607911/1000000000000 : ℝ)*(sp_s0_19) + (56623213/1000000000000 : ℝ)*(sp_s0_20) + (2283215607911/1000000000000 : ℝ)*(f.failure) + (458560513223/100000000000 : ℝ)*(f.sum) + (991125155518759/1000000000000000000000000000 : ℝ)*base62 + (270493048340011/1250000000000000000000000000 : ℝ)*base64 + (1078370547784989/1250000000000000000000000000 : ℝ)*base66 + (1234020896318759/2000000000000000000000000000 : ℝ)*base68 + (409496885873707/10000000000000000000000000000 : ℝ)*base71 + (724219072284989/1250000000000000000000000000 : ℝ)*base72 + (1268067049118759/2000000000000000000000000000 : ℝ)*base74 + (320463238281241/2000000000000000000000000000 : ℝ)*base76 + (565454585097489/625000000000000000000000000 : ℝ)*base78 + (3631/5000000000000000 : ℝ)*base87 + (3631/5000000000000000 : ℝ)*base89 + (3631/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13407/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13407/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1555912588147059747537/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2350957/500000000000 : ℝ)*(base40) + (90140439301/100000000000 : ℝ)*(base50) + (472913482931/500000000000 : ℝ)*(base59) + (998307015591/200000000000 : ℝ)*(major_s0_0) + (998307015591/200000000000 : ℝ)*(major_s0_1) + (998307015591/200000000000 : ℝ)*(major_s0_2) + (400157/500000000000 : ℝ)*(sp_s0_0) + (3059123/100000000000 : ℝ)*(sp_s0_9) + (26611147/500000000000 : ℝ)*(sp_s0_12) + (6574731/200000000000 : ℝ)*(sp_s0_14) + (833083333803/125000000000 : ℝ)*(sp_s0_20) + (6664634597083/1000000000000 : ℝ)*(sp_s0_21) + (1666159219877/250000000000 : ℝ)*(sp_s0_22) + (132733812551/40000000000 : ℝ)*(sp_s0_26) + (3318398536069/1000000000000 : ℝ)*(f.failure) + (3332333735369/500000000000 : ℝ)*(f.sum) + (46673034387149/200000000000000000000000000 : ℝ)*base63 + (39835489388321/250000000000000000000000000 : ℝ)*base65 + (82009145563321/250000000000000000000000000 : ℝ)*base66 + (134332301872851/400000000000000000000000000 : ℝ)*base68 + (1059886843270823/2000000000000000000000000000 : ℝ)*base71 + (73853999963321/250000000000000000000000000 : ℝ)*base72 + (121751797152851/400000000000000000000000000 : ℝ)*base74 + (169633418207149/400000000000000000000000000 : ℝ)*base76 + (12943030961679/125000000000000000000000000 : ℝ)*base79 + (51/5000000000000000 : ℝ)*base86 + (51/5000000000000000 : ℝ)*base88 + (51/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (26329/100000 : ℝ) ^ (131/32 : ℝ) ≤ (42403643997935987/10000000000000000000 : ℝ) := by
    have hpowers : (26329/100000 : ℝ)^131 ≤ (42403643997935987/10000000000000000000 : ℝ)^32 := by
      have hnat : (26329 : ℕ)^131*10000000000000000000^32 ≤ 42403643997935987^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26329 100000 42403643997935987 10000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26329/100000 : ℝ)) (X := (42403643997935987/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (10042403643997935987/10000000000000000000 : ℝ) ≤ (10010341586519043/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (10042403643997935987/10000000000000000000 : ℝ)^32 ≤ (10010341586519043/10000000000000000 : ℝ)^131 := by
      have hnat : (10042403643997935987 : ℕ)^32*10000000000000000^131 ≤ 10010341586519043^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10042403643997935987 10000000000000000000 10010341586519043 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010341586519043/10000000000000000 : ℝ)) (X := (10042403643997935987/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5042403643997935987/5000000000000000000 : ℝ) ≤ (10020650225299349/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (5042403643997935987/5000000000000000000 : ℝ)^32 ≤ (10020650225299349/10000000000000000 : ℝ)^131 := by
      have hnat : (5042403643997935987 : ℕ)^32*10000000000000000^131 ≤ 10020650225299349^131*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5042403643997935987 5000000000000000000 10020650225299349 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020650225299349/10000000000000000 : ℝ)) (X := (5042403643997935987/5000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(10341586519043/2632900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5154319390153/1316450000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (26329/100000 : ℝ)) (alpha := (10341586519043/2632900000000000 : ℝ)) (beta := (5154319390153/1316450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (26329/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(10341586519043/2632900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5154319390153/1316450000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1989/12500 : ℝ) ^ (131/32 : ℝ) ≤ (10791722600267517/20000000000000000000 : ℝ) := by
    have hpowers : (1989/12500 : ℝ)^131 ≤ (10791722600267517/20000000000000000000 : ℝ)^32 := by
      have hnat : (1989 : ℕ)^131*20000000000000000000^32 ≤ 10791722600267517^32*12500^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1989 12500 10791722600267517 20000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1989/12500 : ℝ)) (X := (10791722600267517/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20010791722600267517/20000000000000000000 : ℝ) ≤ (1250164725541631/1250000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (20010791722600267517/20000000000000000000 : ℝ)^32 ≤ (1250164725541631/1250000000000000 : ℝ)^131 := by
      have hnat : (20010791722600267517 : ℕ)^32*1250000000000000^131 ≤ 1250164725541631^131*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010791722600267517 20000000000000000000 1250164725541631 1250000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250164725541631/1250000000000000 : ℝ)) (X := (20010791722600267517/20000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10010791722600267517/10000000000000000000 : ℝ) ≤ (1250329383961573/1250000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (10010791722600267517/10000000000000000000 : ℝ)^32 ≤ (1250329383961573/1250000000000000 : ℝ)^131 := by
      have hnat : (10010791722600267517 : ℕ)^32*1250000000000000^131 ≤ 1250329383961573^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10010791722600267517 10000000000000000000 1250329383961573 1250000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250329383961573/1250000000000000 : ℝ)) (X := (10010791722600267517/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1076637527/1300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(82329209971/99450000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1989/12500 : ℝ)) (alpha := (1076637527/1300000000000 : ℝ)) (beta := (82329209971/99450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1989/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1076637527/1300000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(82329209971/99450000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13407/100000 : ℝ) ^ (131/32 : ℝ) ≤ (13380852402321773/50000000000000000000 : ℝ) := by
    have hpowers : (13407/100000 : ℝ)^131 ≤ (13380852402321773/50000000000000000000 : ℝ)^32 := by
      have hnat : (13407 : ℕ)^131*50000000000000000000^32 ≤ 13380852402321773^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13407 100000 13380852402321773 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13407/100000 : ℝ)) (X := (13380852402321773/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50013380852402321773/50000000000000000000 : ℝ) ≤ (10000653654937861/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50013380852402321773/50000000000000000000 : ℝ)^32 ≤ (10000653654937861/10000000000000000 : ℝ)^131 := by
      have hnat : (50013380852402321773 : ℕ)^32*10000000000000000^131 ≤ 10000653654937861^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013380852402321773 50000000000000000000 10000653654937861 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000653654937861/10000000000000000 : ℝ)) (X := (50013380852402321773/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25013380852402321773/25000000000000000000 : ℝ) ≤ (5000653588863021/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (25013380852402321773/25000000000000000000 : ℝ)^32 ≤ (5000653588863021/5000000000000000 : ℝ)^131 := by
      have hnat : (25013380852402321773 : ℕ)^32*5000000000000000^131 ≤ 5000653588863021^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013380852402321773 25000000000000000000 5000653588863021 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000653588863021/5000000000000000 : ℝ)) (X := (25013380852402321773/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(217884979287/446900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(653522788181/1340700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (13407/100000 : ℝ)) (alpha := (217884979287/446900000000000 : ℝ)) (beta := (653522788181/1340700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (13407/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(217884979287/446900000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(653522788181/1340700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-243564371/500000000 : ℝ)*X 0 0+(1010884997/2500000000 : ℝ)*X 0 1+(4043615673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4187195061/10000000000 : ℝ)*X 1 0+(-3475691169/10000000000 : ℝ)*X 1 1+(5254274707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4187135143/10000000000 : ℝ)*X 2 0+(328394817/625000000 : ℝ)*X 2 1+(-434463311/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1845312113/5000000000 : ℝ)*X 0 0+(4631259611/10000000000 : ℝ)*X 0 1+(4631155999/10000000000 : ℝ)*X 0 2+(1845312113/5000000000 : ℝ)*X 1 0+(4631259611/10000000000 : ℝ)*X 1 1+(4631155999/10000000000 : ℝ)*X 1 2+(1845312113/5000000000 : ℝ)*X 2 0+(4631259611/10000000000 : ℝ)*X 2 1+(4631155999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303025_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15063/2500 : ℝ) < ((-7521/5000 : ℝ)*P 0+(-7521/5000 : ℝ)*P 1+(-7521/5000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15063/2500 : ℝ) < (-568707098558695491188014385709299/95135892150000000000000000000000 : ℝ) := by norm_num
    linear_combination (414233/500000000000 : ℝ)*(base11) + (98519/62500000000 : ℝ)*(base13) + (143329/500000000000 : ℝ)*(base43) + (62965054833/1000000000000 : ℝ)*(base49) + (29955787683/100000000000 : ℝ)*(base50) + (243583/1000000000000 : ℝ)*(base53) + (106935616859/200000000000 : ℝ)*(base59) + (15002915141/50000000000 : ℝ)*(base60) + (7521/5000 : ℝ)*(major_s1_0) + (752099856671/500000000000 : ℝ)*(major_s1_1) + (1504199756417/1000000000000 : ℝ)*(major_s1_2) + (1992610247757/1000000000000 : ℝ)*(sp_s1_0) + (398522587837/200000000000 : ℝ)*(sp_s1_1) + (1992612896111/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (124538323923/62500000000 : ℝ)*(f.sum) + (92897191416347/141700000000000000000000000 : ℝ)*base63 + (5032873421083/32700000000000000000000000 : ℝ)*base65 + (53652579773437/99450000000000000000000000 : ℝ)*base67 + (789486221431/10900000000000000000000000 : ℝ)*base69 + (237978957619159537/860958300000000000000000000000 : ℝ)*base71 + (13598901414289/52658000000000000000000000 : ℝ)*base73 + (83615865319/325000000000000000000000 : ℝ)*base75 + (10893720962023/16455625000000000000000000 : ℝ)*base76 + (620968862078948009/1309209525000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p003_b012 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 25 ≤ c.val) (hhi : c.val < 26)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=25 := by omega
  rcases hc with rfl
  · exact collision_c303025 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 25 ≤ c.val) (hhi : c.val < 26)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b012 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
