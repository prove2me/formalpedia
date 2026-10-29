-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p008_b009
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:26:22.72499+00:00
-- url     : https://prove2.me/submissions/ad63eeea-2f5a-4fb4-8061-aa11db743447

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
theorem collision_support_c308018_s0_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3984969111/10000000000 : ℝ)*x 0 + (702456321/1250000000 : ℝ)*x 1 + (3140659737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3984969111/10000000000 : ℝ)^35 ≤ (15170586080309/50000000000000 : ℝ)^27 := by
    have hnat : (3984969111 : ℕ)^35*50000000000000^27 ≤ 15170586080309^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3984969111 10000000000 15170586080309 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702456321/1250000000 : ℝ)^35 ≤ (47374987447593/100000000000000 : ℝ)^27 := by
    have hnat : (702456321 : ℕ)^35*100000000000000^27 ≤ 47374987447593^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702456321 1250000000 47374987447593 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3140659737/10000000000 : ℝ)^35 ≤ (2785480045549/12500000000000 : ℝ)^27 := by
    have hnat : (3140659737 : ℕ)^35*12500000000000^27 ≤ 2785480045549^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3140659737 10000000000 2785480045549 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3984969111/10000000000 : ℝ), (702456321/1250000000 : ℝ), (3140659737/10000000000 : ℝ)] ![(15170586080309/50000000000000 : ℝ), (47374987447593/100000000000000 : ℝ), (2785480045549/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3984969111/10000000000 : ℝ)|^35 ≤ (15170586080309/50000000000000 : ℝ)^27
        have hw : |(3984969111/10000000000 : ℝ)|=(3984969111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(702456321/1250000000 : ℝ)|^35 ≤ (47374987447593/100000000000000 : ℝ)^27
        have hw : |(702456321/1250000000 : ℝ)|=(702456321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3140659737/10000000000 : ℝ)|^35 ≤ (2785480045549/12500000000000 : ℝ)^27
        have hw : |(3140659737/10000000000 : ℝ)|=(3140659737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-94966831/5000000000 : ℝ)*x 0 + (1675496721/2000000000 : ℝ)*x 1 + (-576066591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94966831/5000000000 : ℝ)^35 ≤ (117378368363/20000000000000 : ℝ)^27 := by
    have hnat : (94966831 : ℕ)^35*20000000000000^27 ≤ 117378368363^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94966831 5000000000 117378368363 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1675496721/2000000000 : ℝ)^35 ≤ (7949364793303/10000000000000 : ℝ)^27 := by
    have hnat : (1675496721 : ℕ)^35*10000000000000^27 ≤ 7949364793303^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675496721 2000000000 7949364793303 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (576066591/2000000000 : ℝ)^35 ≤ (19919460210789/100000000000000 : ℝ)^27 := by
    have hnat : (576066591 : ℕ)^35*100000000000000^27 ≤ 19919460210789^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576066591 2000000000 19919460210789 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94966831/5000000000 : ℝ), (1675496721/2000000000 : ℝ), (-576066591/2000000000 : ℝ)] ![(117378368363/20000000000000 : ℝ), (7949364793303/10000000000000 : ℝ), (19919460210789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94966831/5000000000 : ℝ)|^35 ≤ (117378368363/20000000000000 : ℝ)^27
        have hw : |(-94966831/5000000000 : ℝ)|=(94966831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1675496721/2000000000 : ℝ)|^35 ≤ (7949364793303/10000000000000 : ℝ)^27
        have hw : |(1675496721/2000000000 : ℝ)|=(1675496721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-576066591/2000000000 : ℝ)|^35 ≤ (19919460210789/100000000000000 : ℝ)^27
        have hw : |(-576066591/2000000000 : ℝ)|=(576066591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-5028710153/10000000000 : ℝ)*x 0 + (1769398537/10000000000 : ℝ)*x 1 + (-714016803/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5028710153/10000000000 : ℝ)^35 ≤ (8204068871329/20000000000000 : ℝ)^27 := by
    have hnat : (5028710153 : ℕ)^35*20000000000000^27 ≤ 8204068871329^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028710153 10000000000 8204068871329 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1769398537/10000000000 : ℝ)^35 ≤ (2647885507053/25000000000000 : ℝ)^27 := by
    have hnat : (1769398537 : ℕ)^35*25000000000000^27 ≤ 2647885507053^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769398537 10000000000 2647885507053 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (714016803/1250000000 : ℝ)^35 ≤ (48388113594253/100000000000000 : ℝ)^27 := by
    have hnat : (714016803 : ℕ)^35*100000000000000^27 ≤ 48388113594253^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714016803 1250000000 48388113594253 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5028710153/10000000000 : ℝ), (1769398537/10000000000 : ℝ), (-714016803/1250000000 : ℝ)] ![(8204068871329/20000000000000 : ℝ), (2647885507053/25000000000000 : ℝ), (48388113594253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5028710153/10000000000 : ℝ)|^35 ≤ (8204068871329/20000000000000 : ℝ)^27
        have hw : |(-5028710153/10000000000 : ℝ)|=(5028710153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1769398537/10000000000 : ℝ)|^35 ≤ (2647885507053/25000000000000 : ℝ)^27
        have hw : |(1769398537/10000000000 : ℝ)|=(1769398537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-714016803/1250000000 : ℝ)|^35 ≤ (48388113594253/100000000000000 : ℝ)^27
        have hw : |(-714016803/1250000000 : ℝ)|=(714016803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3126406073/5000000000 : ℝ)*x 0 + (-130577459/5000000000 : ℝ)*x 1 + (-20991577/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3126406073/5000000000 : ℝ)^35 ≤ (5440681114439/10000000000000 : ℝ)^27 := by
    have hnat : (3126406073 : ℕ)^35*10000000000000^27 ≤ 5440681114439^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3126406073 5000000000 5440681114439 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130577459/5000000000 : ℝ)^35 ≤ (443405438643/50000000000000 : ℝ)^27 := by
    have hnat : (130577459 : ℕ)^35*50000000000000^27 ≤ 443405438643^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130577459 5000000000 443405438643 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20991577/39062500 : ℝ)^35 ≤ (44706377963649/100000000000000 : ℝ)^27 := by
    have hnat : (20991577 : ℕ)^35*100000000000000^27 ≤ 44706377963649^27*39062500^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20991577 39062500 44706377963649 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3126406073/5000000000 : ℝ), (-130577459/5000000000 : ℝ), (-20991577/39062500 : ℝ)] ![(5440681114439/10000000000000 : ℝ), (443405438643/50000000000000 : ℝ), (44706377963649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3126406073/5000000000 : ℝ)|^35 ≤ (5440681114439/10000000000000 : ℝ)^27
        have hw : |(3126406073/5000000000 : ℝ)|=(3126406073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130577459/5000000000 : ℝ)|^35 ≤ (443405438643/50000000000000 : ℝ)^27
        have hw : |(-130577459/5000000000 : ℝ)|=(130577459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20991577/39062500 : ℝ)|^35 ≤ (44706377963649/100000000000000 : ℝ)^27
        have hw : |(-20991577/39062500 : ℝ)|=(20991577/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (220238823/1000000000 : ℝ)*x 0 + (894577981/1250000000 : ℝ)*x 1 + (94169551/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220238823/1000000000 : ℝ)^35 ≤ (3516703678601/25000000000000 : ℝ)^27 := by
    have hnat : (220238823 : ℕ)^35*25000000000000^27 ≤ 3516703678601^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220238823 1000000000 3516703678601 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894577981/1250000000 : ℝ)^35 ≤ (12962499784301/20000000000000 : ℝ)^27 := by
    have hnat : (894577981 : ℕ)^35*20000000000000^27 ≤ 12962499784301^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894577981 1250000000 12962499784301 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94169551/312500000 : ℝ)^35 ≤ (21120686345209/100000000000000 : ℝ)^27 := by
    have hnat : (94169551 : ℕ)^35*100000000000000^27 ≤ 21120686345209^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94169551 312500000 21120686345209 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(220238823/1000000000 : ℝ), (894577981/1250000000 : ℝ), (94169551/312500000 : ℝ)] ![(3516703678601/25000000000000 : ℝ), (12962499784301/20000000000000 : ℝ), (21120686345209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(220238823/1000000000 : ℝ)|^35 ≤ (3516703678601/25000000000000 : ℝ)^27
        have hw : |(220238823/1000000000 : ℝ)|=(220238823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(894577981/1250000000 : ℝ)|^35 ≤ (12962499784301/20000000000000 : ℝ)^27
        have hw : |(894577981/1250000000 : ℝ)|=(894577981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94169551/312500000 : ℝ)|^35 ≤ (21120686345209/100000000000000 : ℝ)^27
        have hw : |(94169551/312500000 : ℝ)|=(94169551/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-247196839/10000000000 : ℝ)*x 0 + (1796630567/2000000000 : ℝ)*x 1 + (-1967298379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247196839/10000000000 : ℝ)^35 ≤ (825861992741/100000000000000 : ℝ)^27 := by
    have hnat : (247196839 : ℕ)^35*100000000000000^27 ≤ 825861992741^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247196839 10000000000 825861992741 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1796630567/2000000000 : ℝ)^35 ≤ (87022170488627/100000000000000 : ℝ)^27 := by
    have hnat : (1796630567 : ℕ)^35*100000000000000^27 ≤ 87022170488627^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796630567 2000000000 87022170488627 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1967298379/10000000000 : ℝ)^35 ≤ (12151967511643/100000000000000 : ℝ)^27 := by
    have hnat : (1967298379 : ℕ)^35*100000000000000^27 ≤ 12151967511643^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967298379 10000000000 12151967511643 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-247196839/10000000000 : ℝ), (1796630567/2000000000 : ℝ), (-1967298379/10000000000 : ℝ)] ![(825861992741/100000000000000 : ℝ), (87022170488627/100000000000000 : ℝ), (12151967511643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-247196839/10000000000 : ℝ)|^35 ≤ (825861992741/100000000000000 : ℝ)^27
        have hw : |(-247196839/10000000000 : ℝ)|=(247196839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1796630567/2000000000 : ℝ)|^35 ≤ (87022170488627/100000000000000 : ℝ)^27
        have hw : |(1796630567/2000000000 : ℝ)|=(1796630567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1967298379/10000000000 : ℝ)|^35 ≤ (12151967511643/100000000000000 : ℝ)^27
        have hw : |(-1967298379/10000000000 : ℝ)|=(1967298379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-547385379/1000000000 : ℝ)*x 0 + (209164167/1000000000 : ℝ)*x 1 + (-5032018729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547385379/1000000000 : ℝ)^35 ≤ (45787869389041/100000000000000 : ℝ)^27 := by
    have hnat : (547385379 : ℕ)^35*100000000000000^27 ≤ 45787869389041^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547385379 1000000000 45787869389041 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209164167/1000000000 : ℝ)^35 ≤ (13156797326919/100000000000000 : ℝ)^27 := by
    have hnat : (209164167 : ℕ)^35*100000000000000^27 ≤ 13156797326919^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209164167 1000000000 13156797326919 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5032018729/10000000000 : ℝ)^35 ≤ (2052766663343/5000000000000 : ℝ)^27 := by
    have hnat : (5032018729 : ℕ)^35*5000000000000^27 ≤ 2052766663343^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032018729 10000000000 2052766663343 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547385379/1000000000 : ℝ), (209164167/1000000000 : ℝ), (-5032018729/10000000000 : ℝ)] ![(45787869389041/100000000000000 : ℝ), (13156797326919/100000000000000 : ℝ), (2052766663343/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547385379/1000000000 : ℝ)|^35 ≤ (45787869389041/100000000000000 : ℝ)^27
        have hw : |(-547385379/1000000000 : ℝ)|=(547385379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209164167/1000000000 : ℝ)|^35 ≤ (13156797326919/100000000000000 : ℝ)^27
        have hw : |(209164167/1000000000 : ℝ)|=(209164167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5032018729/10000000000 : ℝ)|^35 ≤ (2052766663343/5000000000000 : ℝ)^27
        have hw : |(-5032018729/10000000000 : ℝ)|=(5032018729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (314742539/500000000 : ℝ)*x 0 + (-516681/250000000 : ℝ)*x 1 + (-1352240149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (314742539/500000000 : ℝ)^35 ≤ (13720362268013/25000000000000 : ℝ)^27 := by
    have hnat : (314742539 : ℕ)^35*25000000000000^27 ≤ 13720362268013^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314742539 500000000 13720362268013 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516681/250000000 : ℝ)^35 ≤ (33098676319/100000000000000 : ℝ)^27 := by
    have hnat : (516681 : ℕ)^35*100000000000000^27 ≤ 33098676319^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516681 250000000 33098676319 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352240149/2500000000 : ℝ)^35 ≤ (2254272611747/5000000000000 : ℝ)^27 := by
    have hnat : (1352240149 : ℕ)^35*5000000000000^27 ≤ 2254272611747^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352240149 2500000000 2254272611747 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(314742539/500000000 : ℝ), (-516681/250000000 : ℝ), (-1352240149/2500000000 : ℝ)] ![(13720362268013/25000000000000 : ℝ), (33098676319/100000000000000 : ℝ), (2254272611747/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(314742539/500000000 : ℝ)|^35 ≤ (13720362268013/25000000000000 : ℝ)^27
        have hw : |(314742539/500000000 : ℝ)|=(314742539/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516681/250000000 : ℝ)|^35 ≤ (33098676319/100000000000000 : ℝ)^27
        have hw : |(-516681/250000000 : ℝ)|=(516681/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1352240149/2500000000 : ℝ)|^35 ≤ (2254272611747/5000000000000 : ℝ)^27
        have hw : |(-1352240149/2500000000 : ℝ)|=(1352240149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (298599191/1250000000 : ℝ)*x 0 + (1354084311/2000000000 : ℝ)*x 1 + (166579409/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (298599191/1250000000 : ℝ)^35 ≤ (3907286426851/25000000000000 : ℝ)^27 := by
    have hnat : (298599191 : ℕ)^35*25000000000000^27 ≤ 3907286426851^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298599191 1250000000 3907286426851 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354084311/2000000000 : ℝ)^35 ≤ (30157669486993/50000000000000 : ℝ)^27 := by
    have hnat : (1354084311 : ℕ)^35*50000000000000^27 ≤ 30157669486993^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354084311 2000000000 30157669486993 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166579409/500000000 : ℝ)^35 ≤ (24055515299947/100000000000000 : ℝ)^27 := by
    have hnat : (166579409 : ℕ)^35*100000000000000^27 ≤ 24055515299947^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166579409 500000000 24055515299947 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(298599191/1250000000 : ℝ), (1354084311/2000000000 : ℝ), (166579409/500000000 : ℝ)] ![(3907286426851/25000000000000 : ℝ), (30157669486993/50000000000000 : ℝ), (24055515299947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(298599191/1250000000 : ℝ)|^35 ≤ (3907286426851/25000000000000 : ℝ)^27
        have hw : |(298599191/1250000000 : ℝ)|=(298599191/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354084311/2000000000 : ℝ)|^35 ≤ (30157669486993/50000000000000 : ℝ)^27
        have hw : |(1354084311/2000000000 : ℝ)|=(1354084311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166579409/500000000 : ℝ)|^35 ≤ (24055515299947/100000000000000 : ℝ)^27
        have hw : |(166579409/500000000 : ℝ)|=(166579409/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-324549599/10000000000 : ℝ)*x 0 + (6548868161/10000000000 : ℝ)*x 1 + (-5032018729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324549599/10000000000 : ℝ)^35 ≤ (587691186949/50000000000000 : ℝ)^27 := by
    have hnat : (324549599 : ℕ)^35*50000000000000^27 ≤ 587691186949^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324549599 10000000000 587691186949 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6548868161/10000000000 : ℝ)^35 ≤ (1805290135851/3125000000000 : ℝ)^27 := by
    have hnat : (6548868161 : ℕ)^35*3125000000000^27 ≤ 1805290135851^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6548868161 10000000000 1805290135851 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5032018729/10000000000 : ℝ)^35 ≤ (2052766663343/5000000000000 : ℝ)^27 := by
    have hnat : (5032018729 : ℕ)^35*5000000000000^27 ≤ 2052766663343^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032018729 10000000000 2052766663343 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-324549599/10000000000 : ℝ), (6548868161/10000000000 : ℝ), (-5032018729/10000000000 : ℝ)] ![(587691186949/50000000000000 : ℝ), (1805290135851/3125000000000 : ℝ), (2052766663343/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-324549599/10000000000 : ℝ)|^35 ≤ (587691186949/50000000000000 : ℝ)^27
        have hw : |(-324549599/10000000000 : ℝ)|=(324549599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6548868161/10000000000 : ℝ)|^35 ≤ (1805290135851/3125000000000 : ℝ)^27
        have hw : |(6548868161/10000000000 : ℝ)|=(6548868161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5032018729/10000000000 : ℝ)|^35 ≤ (2052766663343/5000000000000 : ℝ)^27
        have hw : |(-5032018729/10000000000 : ℝ)|=(5032018729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1600296521/2500000000 : ℝ)*x 0 + (1270979309/5000000000 : ℝ)*x 1 + (-1819609073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1600296521/2500000000 : ℝ)^35 ≤ (56086216235027/100000000000000 : ℝ)^27 := by
    have hnat : (1600296521 : ℕ)^35*100000000000000^27 ≤ 56086216235027^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600296521 2500000000 56086216235027 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270979309/5000000000 : ℝ)^35 ≤ (16940339069597/100000000000000 : ℝ)^27 := by
    have hnat : (1270979309 : ℕ)^35*100000000000000^27 ≤ 16940339069597^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270979309 5000000000 16940339069597 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1819609073/5000000000 : ℝ)^35 ≤ (13486722337797/50000000000000 : ℝ)^27 := by
    have hnat : (1819609073 : ℕ)^35*50000000000000^27 ≤ 13486722337797^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819609073 5000000000 13486722337797 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1600296521/2500000000 : ℝ), (1270979309/5000000000 : ℝ), (-1819609073/5000000000 : ℝ)] ![(56086216235027/100000000000000 : ℝ), (16940339069597/100000000000000 : ℝ), (13486722337797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1600296521/2500000000 : ℝ)|^35 ≤ (56086216235027/100000000000000 : ℝ)^27
        have hw : |(-1600296521/2500000000 : ℝ)|=(1600296521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270979309/5000000000 : ℝ)|^35 ≤ (16940339069597/100000000000000 : ℝ)^27
        have hw : |(1270979309/5000000000 : ℝ)|=(1270979309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1819609073/5000000000 : ℝ)|^35 ≤ (13486722337797/50000000000000 : ℝ)^27
        have hw : |(-1819609073/5000000000 : ℝ)|=(1819609073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5283916581/10000000000 : ℝ)*x 0 + (-30100659/2500000000 : ℝ)*x 1 + (-6387953139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283916581/10000000000 : ℝ)^35 ≤ (21869498887623/50000000000000 : ℝ)^27 := by
    have hnat : (5283916581 : ℕ)^35*50000000000000^27 ≤ 21869498887623^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283916581 10000000000 21869498887623 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30100659/2500000000 : ℝ)^35 ≤ (81259764229/25000000000000 : ℝ)^27 := by
    have hnat : (30100659 : ℕ)^35*25000000000000^27 ≤ 81259764229^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30100659 2500000000 81259764229 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6387953139/10000000000 : ℝ)^35 ≤ (55935963154543/100000000000000 : ℝ)^27 := by
    have hnat : (6387953139 : ℕ)^35*100000000000000^27 ≤ 55935963154543^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6387953139 10000000000 55935963154543 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283916581/10000000000 : ℝ), (-30100659/2500000000 : ℝ), (-6387953139/10000000000 : ℝ)] ![(21869498887623/50000000000000 : ℝ), (81259764229/25000000000000 : ℝ), (55935963154543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283916581/10000000000 : ℝ)|^35 ≤ (21869498887623/50000000000000 : ℝ)^27
        have hw : |(5283916581/10000000000 : ℝ)|=(5283916581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30100659/2500000000 : ℝ)|^35 ≤ (81259764229/25000000000000 : ℝ)^27
        have hw : |(-30100659/2500000000 : ℝ)|=(30100659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6387953139/10000000000 : ℝ)|^35 ≤ (55935963154543/100000000000000 : ℝ)^27
        have hw : |(-6387953139/10000000000 : ℝ)|=(6387953139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6955099141/10000000000 : ℝ)*x 0 + (3485440323/10000000000 : ℝ)*x 1 + (1953062709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6955099141/10000000000 : ℝ)^35 ≤ (62456606579499/100000000000000 : ℝ)^27 := by
    have hnat : (6955099141 : ℕ)^35*100000000000000^27 ≤ 62456606579499^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6955099141 10000000000 62456606579499 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3485440323/10000000000 : ℝ)^35 ≤ (25505291334953/100000000000000 : ℝ)^27 := by
    have hnat : (3485440323 : ℕ)^35*100000000000000^27 ≤ 25505291334953^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3485440323 10000000000 25505291334953 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1953062709/10000000000 : ℝ)^35 ≤ (12038102068391/100000000000000 : ℝ)^27 := by
    have hnat : (1953062709 : ℕ)^35*100000000000000^27 ≤ 12038102068391^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953062709 10000000000 12038102068391 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6955099141/10000000000 : ℝ), (3485440323/10000000000 : ℝ), (1953062709/10000000000 : ℝ)] ![(62456606579499/100000000000000 : ℝ), (25505291334953/100000000000000 : ℝ), (12038102068391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6955099141/10000000000 : ℝ)|^35 ≤ (62456606579499/100000000000000 : ℝ)^27
        have hw : |(6955099141/10000000000 : ℝ)|=(6955099141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3485440323/10000000000 : ℝ)|^35 ≤ (25505291334953/100000000000000 : ℝ)^27
        have hw : |(3485440323/10000000000 : ℝ)|=(3485440323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1953062709/10000000000 : ℝ)|^35 ≤ (12038102068391/100000000000000 : ℝ)^27
        have hw : |(1953062709/10000000000 : ℝ)|=(1953062709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s0_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-219788337/10000000000 : ℝ)*x 0 + (9246652601/10000000000 : ℝ)*x 1 + (-1553233251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219788337/10000000000 : ℝ)^35 ≤ (141832825629/20000000000000 : ℝ)^27 := by
    have hnat : (219788337 : ℕ)^35*20000000000000^27 ≤ 141832825629^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219788337 10000000000 141832825629 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9246652601/10000000000 : ℝ)^35 ≤ (22586341779369/25000000000000 : ℝ)^27 := by
    have hnat : (9246652601 : ℕ)^35*25000000000000^27 ≤ 22586341779369^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9246652601 10000000000 22586341779369 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1553233251/10000000000 : ℝ)^35 ≤ (8945468744757/100000000000000 : ℝ)^27 := by
    have hnat : (1553233251 : ℕ)^35*100000000000000^27 ≤ 8945468744757^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553233251 10000000000 8945468744757 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219788337/10000000000 : ℝ), (9246652601/10000000000 : ℝ), (-1553233251/10000000000 : ℝ)] ![(141832825629/20000000000000 : ℝ), (22586341779369/25000000000000 : ℝ), (8945468744757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219788337/10000000000 : ℝ)|^35 ≤ (141832825629/20000000000000 : ℝ)^27
        have hw : |(-219788337/10000000000 : ℝ)|=(219788337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9246652601/10000000000 : ℝ)|^35 ≤ (22586341779369/25000000000000 : ℝ)^27
        have hw : |(9246652601/10000000000 : ℝ)|=(9246652601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1553233251/10000000000 : ℝ)|^35 ≤ (8945468744757/100000000000000 : ℝ)^27
        have hw : |(-1553233251/10000000000 : ℝ)|=(1553233251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2495473973/5000000000 : ℝ)*x 0 + (879113563/2500000000 : ℝ)*x 1 + (-4309149541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2495473973/5000000000 : ℝ)^35 ≤ (40621484734579/100000000000000 : ℝ)^27 := by
    have hnat : (2495473973 : ℕ)^35*100000000000000^27 ≤ 40621484734579^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495473973 5000000000 40621484734579 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (879113563/2500000000 : ℝ)^35 ≤ (3224984034529/12500000000000 : ℝ)^27 := by
    have hnat : (879113563 : ℕ)^35*12500000000000^27 ≤ 3224984034529^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879113563 2500000000 3224984034529 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4309149541/10000000000 : ℝ)^35 ≤ (4197330370847/12500000000000 : ℝ)^27 := by
    have hnat : (4309149541 : ℕ)^35*12500000000000^27 ≤ 4197330370847^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309149541 10000000000 4197330370847 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2495473973/5000000000 : ℝ), (879113563/2500000000 : ℝ), (-4309149541/10000000000 : ℝ)] ![(40621484734579/100000000000000 : ℝ), (3224984034529/12500000000000 : ℝ), (4197330370847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2495473973/5000000000 : ℝ)|^35 ≤ (40621484734579/100000000000000 : ℝ)^27
        have hw : |(-2495473973/5000000000 : ℝ)|=(2495473973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(879113563/2500000000 : ℝ)|^35 ≤ (3224984034529/12500000000000 : ℝ)^27
        have hw : |(879113563/2500000000 : ℝ)|=(879113563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4309149541/10000000000 : ℝ)|^35 ≤ (4197330370847/12500000000000 : ℝ)^27
        have hw : |(-4309149541/10000000000 : ℝ)|=(4309149541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2327363177/5000000000 : ℝ)*x 0 + (-1492850751/5000000000 : ℝ)*x 1 + (-640381973/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2327363177/5000000000 : ℝ)^35 ≤ (37110125440597/100000000000000 : ℝ)^27 := by
    have hnat : (2327363177 : ℕ)^35*100000000000000^27 ≤ 37110125440597^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2327363177 5000000000 37110125440597 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1492850751/5000000000 : ℝ)^35 ≤ (10434570545693/50000000000000 : ℝ)^27 := by
    have hnat : (1492850751 : ℕ)^35*50000000000000^27 ≤ 10434570545693^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492850751 5000000000 10434570545693 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640381973/1250000000 : ℝ)^35 ≤ (21010366724723/50000000000000 : ℝ)^27 := by
    have hnat : (640381973 : ℕ)^35*50000000000000^27 ≤ 21010366724723^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640381973 1250000000 21010366724723 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2327363177/5000000000 : ℝ), (-1492850751/5000000000 : ℝ), (-640381973/1250000000 : ℝ)] ![(37110125440597/100000000000000 : ℝ), (10434570545693/50000000000000 : ℝ), (21010366724723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2327363177/5000000000 : ℝ)|^35 ≤ (37110125440597/100000000000000 : ℝ)^27
        have hw : |(2327363177/5000000000 : ℝ)|=(2327363177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1492850751/5000000000 : ℝ)|^35 ≤ (10434570545693/50000000000000 : ℝ)^27
        have hw : |(-1492850751/5000000000 : ℝ)|=(1492850751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-640381973/1250000000 : ℝ)|^35 ≤ (21010366724723/50000000000000 : ℝ)^27
        have hw : |(-640381973/1250000000 : ℝ)|=(640381973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4357425509/10000000000 : ℝ)*x 0 + (595754689/1250000000 : ℝ)*x 1 + (1855666237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357425509/10000000000 : ℝ)^35 ≤ (1362683946357/4000000000000 : ℝ)^27 := by
    have hnat : (4357425509 : ℕ)^35*4000000000000^27 ≤ 1362683946357^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357425509 10000000000 1362683946357 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (595754689/1250000000 : ℝ)^35 ≤ (7652911624999/20000000000000 : ℝ)^27 := by
    have hnat : (595754689 : ℕ)^35*20000000000000^27 ≤ 7652911624999^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595754689 1250000000 7652911624999 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1855666237/5000000000 : ℝ)^35 ≤ (3458542899911/12500000000000 : ℝ)^27 := by
    have hnat : (1855666237 : ℕ)^35*12500000000000^27 ≤ 3458542899911^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855666237 5000000000 3458542899911 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357425509/10000000000 : ℝ), (595754689/1250000000 : ℝ), (1855666237/5000000000 : ℝ)] ![(1362683946357/4000000000000 : ℝ), (7652911624999/20000000000000 : ℝ), (3458542899911/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357425509/10000000000 : ℝ)|^35 ≤ (1362683946357/4000000000000 : ℝ)^27
        have hw : |(4357425509/10000000000 : ℝ)|=(4357425509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(595754689/1250000000 : ℝ)|^35 ≤ (7652911624999/20000000000000 : ℝ)^27
        have hw : |(595754689/1250000000 : ℝ)|=(595754689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1855666237/5000000000 : ℝ)|^35 ≤ (3458542899911/12500000000000 : ℝ)^27
        have hw : |(1855666237/5000000000 : ℝ)|=(1855666237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308018_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (760812243/5000000000 : ℝ)*x 0 + (7345793551/10000000000 : ℝ)*x 1 + (-1676060351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760812243/5000000000 : ℝ)^35 ≤ (1742040394663/20000000000000 : ℝ)^27 := by
    have hnat : (760812243 : ℕ)^35*20000000000000^27 ≤ 1742040394663^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760812243 5000000000 1742040394663 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7345793551/10000000000 : ℝ)^35 ≤ (67041926731217/100000000000000 : ℝ)^27 := by
    have hnat : (7345793551 : ℕ)^35*100000000000000^27 ≤ 67041926731217^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7345793551 10000000000 67041926731217 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1676060351/5000000000 : ℝ)^35 ≤ (12123935642269/50000000000000 : ℝ)^27 := by
    have hnat : (1676060351 : ℕ)^35*50000000000000^27 ≤ 12123935642269^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676060351 5000000000 12123935642269 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(760812243/5000000000 : ℝ), (7345793551/10000000000 : ℝ), (-1676060351/5000000000 : ℝ)] ![(1742040394663/20000000000000 : ℝ), (67041926731217/100000000000000 : ℝ), (12123935642269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(760812243/5000000000 : ℝ)|^35 ≤ (1742040394663/20000000000000 : ℝ)^27
        have hw : |(760812243/5000000000 : ℝ)|=(760812243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7345793551/10000000000 : ℝ)|^35 ≤ (67041926731217/100000000000000 : ℝ)^27
        have hw : |(7345793551/10000000000 : ℝ)|=(7345793551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1676060351/5000000000 : ℝ)|^35 ≤ (12123935642269/50000000000000 : ℝ)^27
        have hw : |(-1676060351/5000000000 : ℝ)|=(1676060351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308018 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_2 : ((3984969111/10000000000 : ℝ)*X 2 0+(702456321/1250000000 : ℝ)*X 2 1+(3140659737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((-94966831/5000000000 : ℝ)*X 0 0+(1675496721/2000000000 : ℝ)*X 0 1+(-576066591/2000000000 : ℝ)*X 0 2+(-94966831/5000000000 : ℝ)*X 1 0+(1675496721/2000000000 : ℝ)*X 1 1+(-576066591/2000000000 : ℝ)*X 1 2+(-94966831/5000000000 : ℝ)*X 2 0+(1675496721/2000000000 : ℝ)*X 2 1+(-576066591/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-5028710153/10000000000 : ℝ)*X 0 0+(1769398537/10000000000 : ℝ)*X 0 1+(-714016803/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3126406073/5000000000 : ℝ)*X 1 0+(-130577459/5000000000 : ℝ)*X 1 1+(-20991577/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((220238823/1000000000 : ℝ)*X 2 0+(894577981/1250000000 : ℝ)*X 2 1+(94169551/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-247196839/10000000000 : ℝ)*X 0 0+(1796630567/2000000000 : ℝ)*X 0 1+(-1967298379/10000000000 : ℝ)*X 0 2+(-247196839/10000000000 : ℝ)*X 1 0+(1796630567/2000000000 : ℝ)*X 1 1+(-1967298379/10000000000 : ℝ)*X 1 2+(-247196839/10000000000 : ℝ)*X 2 0+(1796630567/2000000000 : ℝ)*X 2 1+(-1967298379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-547385379/1000000000 : ℝ)*X 0 0+(209164167/1000000000 : ℝ)*X 0 1+(-5032018729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((314742539/500000000 : ℝ)*X 1 0+(-516681/250000000 : ℝ)*X 1 1+(-1352240149/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((298599191/1250000000 : ℝ)*X 2 0+(1354084311/2000000000 : ℝ)*X 2 1+(166579409/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-324549599/10000000000 : ℝ)*X 0 0+(6548868161/10000000000 : ℝ)*X 0 1+(-5032018729/10000000000 : ℝ)*X 0 2+(-324549599/10000000000 : ℝ)*X 1 0+(6548868161/10000000000 : ℝ)*X 1 1+(-5032018729/10000000000 : ℝ)*X 1 2+(-324549599/10000000000 : ℝ)*X 2 0+(6548868161/10000000000 : ℝ)*X 2 1+(-5032018729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1600296521/2500000000 : ℝ)*X 0 0+(1270979309/5000000000 : ℝ)*X 0 1+(-1819609073/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5283916581/10000000000 : ℝ)*X 1 0+(-30100659/2500000000 : ℝ)*X 1 1+(-6387953139/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((6955099141/10000000000 : ℝ)*X 2 0+(3485440323/10000000000 : ℝ)*X 2 1+(1953062709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-219788337/10000000000 : ℝ)*X 0 0+(9246652601/10000000000 : ℝ)*X 0 1+(-1553233251/10000000000 : ℝ)*X 0 2+(-219788337/10000000000 : ℝ)*X 1 0+(9246652601/10000000000 : ℝ)*X 1 1+(-1553233251/10000000000 : ℝ)*X 1 2+(-219788337/10000000000 : ℝ)*X 2 0+(9246652601/10000000000 : ℝ)*X 2 1+(-1553233251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((16913/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16913/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2826273403222888385289/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175913433159/250000000000 : ℝ)*(base7) + (1464279/500000000000 : ℝ)*(base15) + (7297601797/40000000000 : ℝ)*(base44) + (251811166959/1000000000000 : ℝ)*(base50) + (587484367131/1000000000000 : ℝ)*(base53) + (478971/250000000000 : ℝ)*(base60) + (1776665434683/1000000000000 : ℝ)*(major_s0_0) + (797112694879/500000000000 : ℝ)*(major_s0_1) + (37161908361/31250000000 : ℝ)*(major_s0_2) + (16045193/500000000000 : ℝ)*(sp_s0_6) + (349977944559/250000000000 : ℝ)*(sp_s0_7) + (1217468804753/1000000000000 : ℝ)*(sp_s0_8) + (1987396145367/1000000000000 : ℝ)*(sp_s0_9) + (827451272619/500000000000 : ℝ)*(sp_s0_13) + (141715118489/125000000000 : ℝ)*(f.failure) + (1987396145367/1000000000000 : ℝ)*(f.sum) + (192200541153387/1000000000000000000000000000 : ℝ)*base62 + (11837181116107/39062500000000000000000000 : ℝ)*base64 + (289236257282477/625000000000000000000000000 : ℝ)*base66 + (137066159783897/312500000000000000000000000 : ℝ)*base68 + (6919613573997501/10000000000000000000000000000 : ℝ)*base70 + (76047779122271/1250000000000000000000000000 : ℝ)*base72 + (1955898729775417/5000000000000000000000000000 : ℝ)*base75 + (640655329725891/10000000000000000000000000000 : ℝ)*base77 + (5762041627489/50000000000000000000000000 : ℝ)*base78 + (7821/12500000000000000 : ℝ)*base86 + (7821/12500000000000000 : ℝ)*base88 + (7821/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13271/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(13271/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36577307838009201981993/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1793740945567/1000000000000 : ℝ)*(base1) + (39122185697/40000000000 : ℝ)*(base7) + (436263619571/1000000000000 : ℝ)*(base39) + (132283/1000000000000 : ℝ)*(base50) + (328319649333/1000000000000 : ℝ)*(base60) + (1703787471747/1000000000000 : ℝ)*(major_s0_0) + (1703787471747/1000000000000 : ℝ)*(major_s0_1) + (1703787471747/1000000000000 : ℝ)*(major_s0_2) + (1388077/62500000000 : ℝ)*(sp_s0_2) + (7478679/250000000000 : ℝ)*(sp_s0_7) + (1756653496611/500000000000 : ℝ)*(sp_s0_14) + (1719595962371/1000000000000 : ℝ)*(sp_s0_15) + (85978687657/50000000000 : ℝ)*(sp_s0_16) + (10861198237/40000000000 : ℝ)*(sp_s0_20) + (1087216259067/1000000000000 : ℝ)*(f.failure) + (1719595962371/1000000000000 : ℝ)*(f.sum) + (738645700517781/5000000000000000000000000000 : ℝ)*base63 + (115605340769361/1250000000000000000000000000 : ℝ)*base65 + (226722482980639/1250000000000000000000000000 : ℝ)*base67 + (1860696894017781/10000000000000000000000000000 : ℝ)*base69 + (2690927799137107/10000000000000000000000000000 : ℝ)*base71 + (92603790519361/1250000000000000000000000000 : ℝ)*base73 + (5200014397982219/10000000000000000000000000000 : ℝ)*base74 + (5348652600017781/10000000000000000000000000000 : ℝ)*base76 + (1049457859/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (51363/100000000000000000 : ℝ)*base86 + (51363/100000000000000000 : ℝ)*base88 + (51363/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-21607/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-21607/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (63461190182304852195063/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395087615081/1000000000000 : ℝ)*(base1) + (744369377037/1000000000000 : ℝ)*(base7) + (3404129231/250000000000 : ℝ)*(base33) + (1006732768173/1000000000000 : ℝ)*(base44) + (245068358277/1000000000000 : ℝ)*(base50) + (7363/3125000000 : ℝ)*(base60) + (209543480169/100000000000 : ℝ)*(major_s0_0) + (1102318550441/1000000000000 : ℝ)*(major_s0_1) + (1054525659307/500000000000 : ℝ)*(major_s0_2) + (74368209/1000000000000 : ℝ)*(sp_s0_13) + (562028489021/200000000000 : ℝ)*(sp_s0_21) + (697352772463/500000000000 : ℝ)*(sp_s0_22) + (24014383131/10000000000 : ℝ)*(sp_s0_23) + (688296755873/1000000000000 : ℝ)*(sp_s0_27) + (13458221303/10000000000 : ℝ)*(f.failure) + (301881853753/125000000000 : ℝ)*(f.sum) + (440708017143547/2000000000000000000000000000 : ℝ)*base62 + (611349500599641/625000000000000000000000000 : ℝ)*base65 + (248363140419317/1250000000000000000000000000 : ℝ)*base67 + (3870777279979661/5000000000000000000000000000 : ℝ)*base69 + (2827999027951693/5000000000000000000000000000 : ℝ)*base71 + (40551224743253/125000000000000000000000000 : ℝ)*base72 + (5227334019677057/10000000000000000000000000000 : ℝ)*base74 + (443208673230913/1000000000000000000000000000 : ℝ)*base77 + (400819358236787/1250000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (433/1000000000000000 : ℝ)*base87 + (433/1000000000000000 : ℝ)*base89 + (433/1000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (16913/20000 : ℝ) ^ (17/4 : ℝ) ≤ (49041108266073858489/100000000000000000000 : ℝ) := by
    have hpowers : (16913/20000 : ℝ)^17 ≤ (49041108266073858489/100000000000000000000 : ℝ)^4 := by
      have hnat : (16913 : ℕ)^17*100000000000000000000^4 ≤ 49041108266073858489^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16913 20000 49041108266073858489 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16913/20000 : ℝ)) (X := (49041108266073858489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (149041108266073858489/100000000000000000000 : ℝ) ≤ (5492219723878561/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (149041108266073858489/100000000000000000000 : ℝ)^4 ≤ (5492219723878561/5000000000000000 : ℝ)^17 := by
      have hnat : (149041108266073858489 : ℕ)^4*5000000000000000^17 ≤ 5492219723878561^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        149041108266073858489 100000000000000000000 5492219723878561 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5492219723878561/5000000000000000 : ℝ)) (X := (149041108266073858489/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (99041108266073858489/50000000000000000000 : ℝ) ≤ (367025313795503/312500000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (99041108266073858489/50000000000000000000 : ℝ)^4 ≤ (367025313795503/312500000000000 : ℝ)^17 := by
      have hnat : (99041108266073858489 : ℕ)^4*312500000000000^17 ≤ 367025313795503^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        99041108266073858489 50000000000000000000 367025313795503 312500000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (367025313795503/312500000000000 : ℝ)) (X := (99041108266073858489/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(492219723878561/4228250000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(380185296849487/4228250000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (16913/20000 : ℝ)) (alpha := (492219723878561/4228250000000000 : ℝ)) (beta := (380185296849487/4228250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16913/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(492219723878561/4228250000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(380185296849487/4228250000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (13271/20000 : ℝ) ^ (17/4 : ℝ) ≤ (17496977261007600511/100000000000000000000 : ℝ) := by
    have hpowers : (13271/20000 : ℝ)^17 ≤ (17496977261007600511/100000000000000000000 : ℝ)^4 := by
      have hnat : (13271 : ℕ)^17*100000000000000000000^4 ≤ 17496977261007600511^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13271 20000 17496977261007600511 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13271/20000 : ℝ)) (X := (17496977261007600511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (117496977261007600511/100000000000000000000 : ℝ) ≤ (2077336561575539/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (117496977261007600511/100000000000000000000 : ℝ)^4 ≤ (2077336561575539/2000000000000000 : ℝ)^17 := by
      have hnat : (117496977261007600511 : ℕ)^4*2000000000000000^17 ≤ 2077336561575539^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117496977261007600511 100000000000000000000 2077336561575539 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2077336561575539/2000000000000000 : ℝ)) (X := (117496977261007600511/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (67496977261007600511/50000000000000000000 : ℝ) ≤ (1073154356375589/1000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (67496977261007600511/50000000000000000000 : ℝ)^4 ≤ (1073154356375589/1000000000000000 : ℝ)^17 := by
      have hnat : (67496977261007600511 : ℕ)^4*1000000000000000^17 ≤ 1073154356375589^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67496977261007600511 50000000000000000000 1073154356375589 1000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1073154356375589/1000000000000000 : ℝ)) (X := (67496977261007600511/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(77336561575539/1327100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(68972151175639/1327100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (13271/20000 : ℝ)) (alpha := (77336561575539/1327100000000000 : ℝ)) (beta := (68972151175639/1327100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (13271/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(77336561575539/1327100000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(68972151175639/1327100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (21607/25000 : ℝ) ^ (17/4 : ℝ) ≤ (13449975013292636733/25000000000000000000 : ℝ) := by
    have hpowers : (21607/25000 : ℝ)^17 ≤ (13449975013292636733/25000000000000000000 : ℝ)^4 := by
      have hnat : (21607 : ℕ)^17*25000000000000000000^4 ≤ 13449975013292636733^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21607 25000 13449975013292636733 25000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21607/25000 : ℝ)) (X := (13449975013292636733/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (38449975013292636733/25000000000000000000 : ℝ) ≤ (11065974359289961/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (38449975013292636733/25000000000000000000 : ℝ)^4 ≤ (11065974359289961/10000000000000000 : ℝ)^17 := by
      have hnat : (38449975013292636733 : ℕ)^4*10000000000000000^17 ≤ 11065974359289961^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38449975013292636733 25000000000000000000 11065974359289961 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11065974359289961/10000000000000000 : ℝ)) (X := (38449975013292636733/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25949975013292636733/12500000000000000000 : ℝ) ≤ (11875219090143641/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (25949975013292636733/12500000000000000000 : ℝ)^4 ≤ (11875219090143641/10000000000000000 : ℝ)^17 := by
      have hnat : (25949975013292636733 : ℕ)^4*10000000000000000^17 ≤ 11875219090143641^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25949975013292636733 12500000000000000000 11875219090143641 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11875219090143641/10000000000000000 : ℝ)) (X := (25949975013292636733/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1065974359289961/8642800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(10115559135671/108035000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (21607/25000 : ℝ)) (alpha := (1065974359289961/8642800000000000 : ℝ)) (beta := (10115559135671/108035000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (21607/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1065974359289961/8642800000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(10115559135671/108035000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2495473973/5000000000 : ℝ)*X 0 0+(879113563/2500000000 : ℝ)*X 0 1+(-4309149541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2327363177/5000000000 : ℝ)*X 1 0+(-1492850751/5000000000 : ℝ)*X 1 1+(-640381973/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4357425509/10000000000 : ℝ)*X 2 0+(595754689/1250000000 : ℝ)*X 2 1+(1855666237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((760812243/5000000000 : ℝ)*X 0 0+(7345793551/10000000000 : ℝ)*X 0 1+(-1676060351/5000000000 : ℝ)*X 0 2+(760812243/5000000000 : ℝ)*X 1 0+(7345793551/10000000000 : ℝ)*X 1 1+(-1676060351/5000000000 : ℝ)*X 1 2+(760812243/5000000000 : ℝ)*X 2 0+(7345793551/10000000000 : ℝ)*X 2 1+(-1676060351/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308018_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-320133/50000 : ℝ) < ((-156711/100000 : ℝ)*P 0+(-156711/100000 : ℝ)*P 1+(-156711/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-320133/50000 : ℝ) < (-154918012833606160131426149712600951/24248717518805000000000000000000000 : ℝ) := by norm_num
    linear_combination (1649/20000000000 : ℝ)*(base1) + (151601/1000000000000 : ℝ)*(base15) + (377143/1000000000000 : ℝ)*(base23) + (18329/25000000000 : ℝ)*(base29) + (32493/200000000000 : ℝ)*(base39) + (395680533411/1000000000000 : ℝ)*(base50) + (198533/1000000000000 : ℝ)*(base53) + (23040906031/100000000000 : ℝ)*(base60) + (156711/100000 : ℝ)*(major_s1_0) + (156711/100000 : ℝ)*(major_s1_1) + (1567109801467/1000000000000 : ℝ)*(major_s1_2) + (532392432261/250000000000 : ℝ)*(sp_s1_0) + (1064784747497/500000000000 : ℝ)*(sp_s1_1) + (133098091749/62500000000 : ℝ)*(sp_s1_2) + (99999918439/100000000000 : ℝ)*(sp_s1_6) + (266196230641/125000000000 : ℝ)*(f.sum) + (16288593042505226357/114698598800000000000000000000000 : ℝ)*base62 + (41495197196517/54017500000000000000000000 : ℝ)*base65 + (6075327082533/16588750000000000000000000 : ℝ)*base67 + (2080028927686733/8642800000000000000000000000 : ℝ)*base69 + (13011326030946813/18271959550000000000000000000 : ℝ)*base71 + (3401837695903/42282500000000000000000000 : ℝ)*base72 + (5611560105579/33177500000000000000000000 : ℝ)*base74 + (52948330751363/84565000000000000000000000 : ℝ)*base77 + (94455162137962243/561131057500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p008_b009 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (c : Fin 88) (hlo : 18 ≤ c.val) (hhi : c.val < 19)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=18 := by omega
  rcases hc with rfl
  · exact collision_c308018 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (c : Fin 88) (hlo : 18 ≤ c.val) (hhi : c.val < 19)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p008_b009 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
