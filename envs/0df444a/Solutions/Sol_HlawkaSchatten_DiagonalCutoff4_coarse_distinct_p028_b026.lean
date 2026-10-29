-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b026
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:21:54.022177+00:00
-- url     : https://prove2.me/submissions/af264c53-eb64-429f-9e4f-f27c2843f72e

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
theorem collision_support_c328056_s0_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-116026531/400000000 : ℝ)*x 0 + (11602653/40000000 : ℝ)*x 1 + (-6108852343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116026531/400000000 : ℝ)^93 ≤ (2803615550193/12500000000000 : ℝ)^77 := by
    have hnat : (116026531 : ℕ)^93*12500000000000^77 ≤ 2803615550193^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116026531 400000000 2803615550193 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11602653/40000000 : ℝ)^93 ≤ (5607231042017/25000000000000 : ℝ)^77 := by
    have hnat : (11602653 : ℕ)^93*25000000000000^77 ≤ 5607231042017^77*40000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11602653 40000000 5607231042017 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6108852343/10000000000 : ℝ)^93 ≤ (27571075708609/50000000000000 : ℝ)^77 := by
    have hnat : (6108852343 : ℕ)^93*50000000000000^77 ≤ 27571075708609^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6108852343 10000000000 27571075708609 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116026531/400000000 : ℝ), (11602653/40000000 : ℝ), (-6108852343/10000000000 : ℝ)] ![(2803615550193/12500000000000 : ℝ), (5607231042017/25000000000000 : ℝ), (27571075708609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116026531/400000000 : ℝ)|^93 ≤ (2803615550193/12500000000000 : ℝ)^77
        have hw : |(-116026531/400000000 : ℝ)|=(116026531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(11602653/40000000 : ℝ)|^93 ≤ (5607231042017/25000000000000 : ℝ)^77
        have hw : |(11602653/40000000 : ℝ)|=(11602653/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6108852343/10000000000 : ℝ)|^93 ≤ (27571075708609/50000000000000 : ℝ)^77
        have hw : |(-6108852343/10000000000 : ℝ)|=(6108852343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s0_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (116026531/400000000 : ℝ)*x 0 + (-2900663249/10000000000 : ℝ)*x 1 + (-6108852343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116026531/400000000 : ℝ)^93 ≤ (2803615550193/12500000000000 : ℝ)^77 := by
    have hnat : (116026531 : ℕ)^93*12500000000000^77 ≤ 2803615550193^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116026531 400000000 2803615550193 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2900663249/10000000000 : ℝ)^93 ≤ (2803615519841/12500000000000 : ℝ)^77 := by
    have hnat : (2900663249 : ℕ)^93*12500000000000^77 ≤ 2803615519841^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2900663249 10000000000 2803615519841 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6108852343/10000000000 : ℝ)^93 ≤ (27571075708609/50000000000000 : ℝ)^77 := by
    have hnat : (6108852343 : ℕ)^93*50000000000000^77 ≤ 27571075708609^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6108852343 10000000000 27571075708609 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(116026531/400000000 : ℝ), (-2900663249/10000000000 : ℝ), (-6108852343/10000000000 : ℝ)] ![(2803615550193/12500000000000 : ℝ), (2803615519841/12500000000000 : ℝ), (27571075708609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(116026531/400000000 : ℝ)|^93 ≤ (2803615550193/12500000000000 : ℝ)^77
        have hw : |(116026531/400000000 : ℝ)|=(116026531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2900663249/10000000000 : ℝ)|^93 ≤ (2803615519841/12500000000000 : ℝ)^77
        have hw : |(-2900663249/10000000000 : ℝ)|=(2900663249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6108852343/10000000000 : ℝ)|^93 ≤ (27571075708609/50000000000000 : ℝ)^77
        have hw : |(-6108852343/10000000000 : ℝ)|=(6108852343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s0_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-280873027/1250000000 : ℝ)*x 0 + (606411893/5000000000 : ℝ)*x 1 + (-1985339033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280873027/1250000000 : ℝ)^93 ≤ (8238299244439/50000000000000 : ℝ)^77 := by
    have hnat : (280873027 : ℕ)^93*50000000000000^77 ≤ 8238299244439^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280873027 1250000000 8238299244439 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (606411893/5000000000 : ℝ)^93 ≤ (1564760966511/20000000000000 : ℝ)^77 := by
    have hnat : (606411893 : ℕ)^93*20000000000000^77 ≤ 1564760966511^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606411893 5000000000 1564760966511 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1985339033/2500000000 : ℝ)^93 ≤ (37849798327379/50000000000000 : ℝ)^77 := by
    have hnat : (1985339033 : ℕ)^93*50000000000000^77 ≤ 37849798327379^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985339033 2500000000 37849798327379 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-280873027/1250000000 : ℝ), (606411893/5000000000 : ℝ), (-1985339033/2500000000 : ℝ)] ![(8238299244439/50000000000000 : ℝ), (1564760966511/20000000000000 : ℝ), (37849798327379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-280873027/1250000000 : ℝ)|^93 ≤ (8238299244439/50000000000000 : ℝ)^77
        have hw : |(-280873027/1250000000 : ℝ)|=(280873027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(606411893/5000000000 : ℝ)|^93 ≤ (1564760966511/20000000000000 : ℝ)^77
        have hw : |(606411893/5000000000 : ℝ)|=(606411893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1985339033/2500000000 : ℝ)|^93 ≤ (37849798327379/50000000000000 : ℝ)^77
        have hw : |(-1985339033/2500000000 : ℝ)|=(1985339033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s0_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1123491999/5000000000 : ℝ)*x 0 + (-303205917/2500000000 : ℝ)*x 1 + (-7941356381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123491999/5000000000 : ℝ)^93 ≤ (4119149139543/25000000000000 : ℝ)^77 := by
    have hnat : (1123491999 : ℕ)^93*25000000000000^77 ≤ 4119149139543^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123491999 5000000000 4119149139543 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303205917/2500000000 : ℝ)^93 ≤ (977975489147/12500000000000 : ℝ)^77 := by
    have hnat : (303205917 : ℕ)^93*12500000000000^77 ≤ 977975489147^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303205917 2500000000 977975489147 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7941356381/10000000000 : ℝ)^93 ≤ (9462449940189/12500000000000 : ℝ)^77 := by
    have hnat : (7941356381 : ℕ)^93*12500000000000^77 ≤ 9462449940189^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7941356381 10000000000 9462449940189 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1123491999/5000000000 : ℝ), (-303205917/2500000000 : ℝ), (-7941356381/10000000000 : ℝ)] ![(4119149139543/25000000000000 : ℝ), (977975489147/12500000000000 : ℝ), (9462449940189/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1123491999/5000000000 : ℝ)|^93 ≤ (4119149139543/25000000000000 : ℝ)^77
        have hw : |(1123491999/5000000000 : ℝ)|=(1123491999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-303205917/2500000000 : ℝ)|^93 ≤ (977975489147/12500000000000 : ℝ)^77
        have hw : |(-303205917/2500000000 : ℝ)|=(303205917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7941356381/10000000000 : ℝ)|^93 ≤ (9462449940189/12500000000000 : ℝ)^77
        have hw : |(-7941356381/10000000000 : ℝ)|=(7941356381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s0_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3337620731/10000000000 : ℝ)*x 0 + (7380177367/10000000000 : ℝ)*x 1 + (17907239/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3337620731/10000000000 : ℝ)^93 ≤ (6642795943389/25000000000000 : ℝ)^77 := by
    have hnat : (3337620731 : ℕ)^93*25000000000000^77 ≤ 6642795943389^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3337620731 10000000000 6642795943389 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7380177367/10000000000 : ℝ)^93 ≤ (69287055944041/100000000000000 : ℝ)^77 := by
    have hnat : (7380177367 : ℕ)^93*100000000000000^77 ≤ 69287055944041^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7380177367 10000000000 69287055944041 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17907239/250000000 : ℝ)^93 ≤ (4141760273873/100000000000000 : ℝ)^77 := by
    have hnat : (17907239 : ℕ)^93*100000000000000^77 ≤ 4141760273873^77*250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17907239 250000000 4141760273873 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3337620731/10000000000 : ℝ), (7380177367/10000000000 : ℝ), (17907239/250000000 : ℝ)] ![(6642795943389/25000000000000 : ℝ), (69287055944041/100000000000000 : ℝ), (4141760273873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3337620731/10000000000 : ℝ)|^93 ≤ (6642795943389/25000000000000 : ℝ)^77
        have hw : |(3337620731/10000000000 : ℝ)|=(3337620731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7380177367/10000000000 : ℝ)|^93 ≤ (69287055944041/100000000000000 : ℝ)^77
        have hw : |(7380177367/10000000000 : ℝ)|=(7380177367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17907239/250000000 : ℝ)|^93 ≤ (4141760273873/100000000000000 : ℝ)^77
        have hw : |(17907239/250000000 : ℝ)|=(17907239/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s0_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-303205917/2500000000 : ℝ)*x 0 + (1123491999/5000000000 : ℝ)*x 1 + (-7941356381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (303205917/2500000000 : ℝ)^93 ≤ (977975489147/12500000000000 : ℝ)^77 := by
    have hnat : (303205917 : ℕ)^93*12500000000000^77 ≤ 977975489147^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303205917 2500000000 977975489147 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123491999/5000000000 : ℝ)^93 ≤ (4119149139543/25000000000000 : ℝ)^77 := by
    have hnat : (1123491999 : ℕ)^93*25000000000000^77 ≤ 4119149139543^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123491999 5000000000 4119149139543 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7941356381/10000000000 : ℝ)^93 ≤ (9462449940189/12500000000000 : ℝ)^77 := by
    have hnat : (7941356381 : ℕ)^93*12500000000000^77 ≤ 9462449940189^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7941356381 10000000000 9462449940189 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-303205917/2500000000 : ℝ), (1123491999/5000000000 : ℝ), (-7941356381/10000000000 : ℝ)] ![(977975489147/12500000000000 : ℝ), (4119149139543/25000000000000 : ℝ), (9462449940189/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-303205917/2500000000 : ℝ)|^93 ≤ (977975489147/12500000000000 : ℝ)^77
        have hw : |(-303205917/2500000000 : ℝ)|=(303205917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123491999/5000000000 : ℝ)|^93 ≤ (4119149139543/25000000000000 : ℝ)^77
        have hw : |(1123491999/5000000000 : ℝ)|=(1123491999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7941356381/10000000000 : ℝ)|^93 ≤ (9462449940189/12500000000000 : ℝ)^77
        have hw : |(-7941356381/10000000000 : ℝ)|=(7941356381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s0_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (606411893/5000000000 : ℝ)*x 0 + (-280873027/1250000000 : ℝ)*x 1 + (-1985339033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (606411893/5000000000 : ℝ)^93 ≤ (1564760966511/20000000000000 : ℝ)^77 := by
    have hnat : (606411893 : ℕ)^93*20000000000000^77 ≤ 1564760966511^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606411893 5000000000 1564760966511 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280873027/1250000000 : ℝ)^93 ≤ (8238299244439/50000000000000 : ℝ)^77 := by
    have hnat : (280873027 : ℕ)^93*50000000000000^77 ≤ 8238299244439^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280873027 1250000000 8238299244439 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1985339033/2500000000 : ℝ)^93 ≤ (37849798327379/50000000000000 : ℝ)^77 := by
    have hnat : (1985339033 : ℕ)^93*50000000000000^77 ≤ 37849798327379^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985339033 2500000000 37849798327379 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(606411893/5000000000 : ℝ), (-280873027/1250000000 : ℝ), (-1985339033/2500000000 : ℝ)] ![(1564760966511/20000000000000 : ℝ), (8238299244439/50000000000000 : ℝ), (37849798327379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(606411893/5000000000 : ℝ)|^93 ≤ (1564760966511/20000000000000 : ℝ)^77
        have hw : |(606411893/5000000000 : ℝ)|=(606411893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-280873027/1250000000 : ℝ)|^93 ≤ (8238299244439/50000000000000 : ℝ)^77
        have hw : |(-280873027/1250000000 : ℝ)|=(280873027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1985339033/2500000000 : ℝ)|^93 ≤ (37849798327379/50000000000000 : ℝ)^77
        have hw : |(-1985339033/2500000000 : ℝ)|=(1985339033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s0_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7380177367/10000000000 : ℝ)*x 0 + (3337620731/10000000000 : ℝ)*x 1 + (17907239/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7380177367/10000000000 : ℝ)^93 ≤ (69287055944041/100000000000000 : ℝ)^77 := by
    have hnat : (7380177367 : ℕ)^93*100000000000000^77 ≤ 69287055944041^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7380177367 10000000000 69287055944041 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3337620731/10000000000 : ℝ)^93 ≤ (6642795943389/25000000000000 : ℝ)^77 := by
    have hnat : (3337620731 : ℕ)^93*25000000000000^77 ≤ 6642795943389^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3337620731 10000000000 6642795943389 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17907239/250000000 : ℝ)^93 ≤ (4141760273873/100000000000000 : ℝ)^77 := by
    have hnat : (17907239 : ℕ)^93*100000000000000^77 ≤ 4141760273873^77*250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17907239 250000000 4141760273873 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7380177367/10000000000 : ℝ), (3337620731/10000000000 : ℝ), (17907239/250000000 : ℝ)] ![(69287055944041/100000000000000 : ℝ), (6642795943389/25000000000000 : ℝ), (4141760273873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7380177367/10000000000 : ℝ)|^93 ≤ (69287055944041/100000000000000 : ℝ)^77
        have hw : |(7380177367/10000000000 : ℝ)|=(7380177367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3337620731/10000000000 : ℝ)|^93 ≤ (6642795943389/25000000000000 : ℝ)^77
        have hw : |(3337620731/10000000000 : ℝ)|=(3337620731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17907239/250000000 : ℝ)|^93 ≤ (4141760273873/100000000000000 : ℝ)^77
        have hw : |(17907239/250000000 : ℝ)|=(17907239/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s0_19 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2062024529/5000000000 : ℝ)*x 0 + (1931293829/10000000000 : ℝ)*x 1 + (-5816342813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062024529/5000000000 : ℝ)^93 ≤ (34307661047849/100000000000000 : ℝ)^77 := by
    have hnat : (2062024529 : ℕ)^93*100000000000000^77 ≤ 34307661047849^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062024529 5000000000 34307661047849 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931293829/10000000000 : ℝ)^93 ≤ (1715391360137/12500000000000 : ℝ)^77 := by
    have hnat : (1931293829 : ℕ)^93*12500000000000^77 ≤ 1715391360137^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931293829 10000000000 1715391360137 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5816342813/10000000000 : ℝ)^93 ≤ (25984604027123/50000000000000 : ℝ)^77 := by
    have hnat : (5816342813 : ℕ)^93*50000000000000^77 ≤ 25984604027123^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5816342813 10000000000 25984604027123 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2062024529/5000000000 : ℝ), (1931293829/10000000000 : ℝ), (-5816342813/10000000000 : ℝ)] ![(34307661047849/100000000000000 : ℝ), (1715391360137/12500000000000 : ℝ), (25984604027123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2062024529/5000000000 : ℝ)|^93 ≤ (34307661047849/100000000000000 : ℝ)^77
        have hw : |(-2062024529/5000000000 : ℝ)|=(2062024529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1931293829/10000000000 : ℝ)|^93 ≤ (1715391360137/12500000000000 : ℝ)^77
        have hw : |(1931293829/10000000000 : ℝ)|=(1931293829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5816342813/10000000000 : ℝ)|^93 ≤ (25984604027123/50000000000000 : ℝ)^77
        have hw : |(-5816342813/10000000000 : ℝ)|=(5816342813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s0_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (965646677/5000000000 : ℝ)*x 0 + (-412404911/1000000000 : ℝ)*x 1 + (-2908171571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (965646677/5000000000 : ℝ)^93 ≤ (6861563402283/50000000000000 : ℝ)^77 := by
    have hnat : (965646677 : ℕ)^93*50000000000000^77 ≤ 6861563402283^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965646677 5000000000 6861563402283 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412404911/1000000000 : ℝ)^93 ≤ (34307661570321/100000000000000 : ℝ)^77 := by
    have hnat : (412404911 : ℕ)^93*100000000000000^77 ≤ 34307661570321^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412404911 1000000000 34307661570321 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2908171571/5000000000 : ℝ)^93 ≤ (51969211604703/100000000000000 : ℝ)^77 := by
    have hnat : (2908171571 : ℕ)^93*100000000000000^77 ≤ 51969211604703^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2908171571 5000000000 51969211604703 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(965646677/5000000000 : ℝ), (-412404911/1000000000 : ℝ), (-2908171571/5000000000 : ℝ)] ![(6861563402283/50000000000000 : ℝ), (34307661570321/100000000000000 : ℝ), (51969211604703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(965646677/5000000000 : ℝ)|^93 ≤ (6861563402283/50000000000000 : ℝ)^77
        have hw : |(965646677/5000000000 : ℝ)|=(965646677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-412404911/1000000000 : ℝ)|^93 ≤ (34307661570321/100000000000000 : ℝ)^77
        have hw : |(-412404911/1000000000 : ℝ)|=(412404911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2908171571/5000000000 : ℝ)|^93 ≤ (51969211604703/100000000000000 : ℝ)^77
        have hw : |(-2908171571/5000000000 : ℝ)|=(2908171571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s0_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5411661311/10000000000 : ℝ)*x 0 + (5411661211/10000000000 : ℝ)*x 1 + (399885079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411661311/10000000000 : ℝ)^93 ≤ (47634190241699/100000000000000 : ℝ)^77 := by
    have hnat : (5411661311 : ℕ)^93*100000000000000^77 ≤ 47634190241699^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411661311 10000000000 47634190241699 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411661211/10000000000 : ℝ)^93 ≤ (5954273647323/12500000000000 : ℝ)^77 := by
    have hnat : (5411661211 : ℕ)^93*12500000000000^77 ≤ 5954273647323^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411661211 10000000000 5954273647323 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399885079/5000000000 : ℝ)^93 ≤ (1182905142229/25000000000000 : ℝ)^77 := by
    have hnat : (399885079 : ℕ)^93*25000000000000^77 ≤ 1182905142229^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399885079 5000000000 1182905142229 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411661311/10000000000 : ℝ), (5411661211/10000000000 : ℝ), (399885079/5000000000 : ℝ)] ![(47634190241699/100000000000000 : ℝ), (5954273647323/12500000000000 : ℝ), (1182905142229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411661311/10000000000 : ℝ)|^93 ≤ (47634190241699/100000000000000 : ℝ)^77
        have hw : |(5411661311/10000000000 : ℝ)|=(5411661311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411661211/10000000000 : ℝ)|^93 ≤ (5954273647323/12500000000000 : ℝ)^77
        have hw : |(5411661211/10000000000 : ℝ)|=(5411661211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(399885079/5000000000 : ℝ)|^93 ≤ (1182905142229/25000000000000 : ℝ)^77
        have hw : |(399885079/5000000000 : ℝ)|=(399885079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s1_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3233966383/10000000000 : ℝ)*x 0 + (1616989717/5000000000 : ℝ)*x 1 + (-2762624293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3233966383/10000000000 : ℝ)^93 ≤ (25577751194547/100000000000000 : ℝ)^77 := by
    have hnat : (3233966383 : ℕ)^93*100000000000000^77 ≤ 25577751194547^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3233966383 10000000000 25577751194547 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1616989717/5000000000 : ℝ)^93 ≤ (25577875864861/100000000000000 : ℝ)^77 := by
    have hnat : (1616989717 : ℕ)^93*100000000000000^77 ≤ 25577875864861^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616989717 5000000000 25577875864861 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2762624293/5000000000 : ℝ)^93 ≤ (24422186461363/50000000000000 : ℝ)^77 := by
    have hnat : (2762624293 : ℕ)^93*50000000000000^77 ≤ 24422186461363^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762624293 5000000000 24422186461363 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3233966383/10000000000 : ℝ), (1616989717/5000000000 : ℝ), (-2762624293/5000000000 : ℝ)] ![(25577751194547/100000000000000 : ℝ), (25577875864861/100000000000000 : ℝ), (24422186461363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3233966383/10000000000 : ℝ)|^93 ≤ (25577751194547/100000000000000 : ℝ)^77
        have hw : |(-3233966383/10000000000 : ℝ)|=(3233966383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1616989717/5000000000 : ℝ)|^93 ≤ (25577875864861/100000000000000 : ℝ)^77
        have hw : |(1616989717/5000000000 : ℝ)|=(1616989717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2762624293/5000000000 : ℝ)|^93 ≤ (24422186461363/50000000000000 : ℝ)^77
        have hw : |(-2762624293/5000000000 : ℝ)|=(2762624293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s1_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3233966383/10000000000 : ℝ)*x 0 + (-1616989717/5000000000 : ℝ)*x 1 + (-2762624293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3233966383/10000000000 : ℝ)^93 ≤ (25577751194547/100000000000000 : ℝ)^77 := by
    have hnat : (3233966383 : ℕ)^93*100000000000000^77 ≤ 25577751194547^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3233966383 10000000000 25577751194547 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1616989717/5000000000 : ℝ)^93 ≤ (25577875864861/100000000000000 : ℝ)^77 := by
    have hnat : (1616989717 : ℕ)^93*100000000000000^77 ≤ 25577875864861^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616989717 5000000000 25577875864861 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2762624293/5000000000 : ℝ)^93 ≤ (24422186461363/50000000000000 : ℝ)^77 := by
    have hnat : (2762624293 : ℕ)^93*50000000000000^77 ≤ 24422186461363^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762624293 5000000000 24422186461363 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3233966383/10000000000 : ℝ), (-1616989717/5000000000 : ℝ), (-2762624293/5000000000 : ℝ)] ![(25577751194547/100000000000000 : ℝ), (25577875864861/100000000000000 : ℝ), (24422186461363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3233966383/10000000000 : ℝ)|^93 ≤ (25577751194547/100000000000000 : ℝ)^77
        have hw : |(3233966383/10000000000 : ℝ)|=(3233966383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1616989717/5000000000 : ℝ)|^93 ≤ (25577875864861/100000000000000 : ℝ)^77
        have hw : |(-1616989717/5000000000 : ℝ)|=(1616989717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2762624293/5000000000 : ℝ)|^93 ≤ (24422186461363/50000000000000 : ℝ)^77
        have hw : |(-2762624293/5000000000 : ℝ)|=(2762624293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5118153249/10000000000 : ℝ)*x 0 + (2559084119/5000000000 : ℝ)*x 1 + (1600407597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5118153249/10000000000 : ℝ)^93 ≤ (8906340373473/20000000000000 : ℝ)^77 := by
    have hnat : (5118153249 : ℕ)^93*20000000000000^77 ≤ 8906340373473^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5118153249 10000000000 8906340373473 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2559084119/5000000000 : ℝ)^93 ≤ (44531859382041/100000000000000 : ℝ)^77 := by
    have hnat : (2559084119 : ℕ)^93*100000000000000^77 ≤ 44531859382041^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559084119 5000000000 44531859382041 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1600407597/10000000000 : ℝ)^93 ≤ (5468219370297/50000000000000 : ℝ)^77 := by
    have hnat : (1600407597 : ℕ)^93*50000000000000^77 ≤ 5468219370297^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600407597 10000000000 5468219370297 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5118153249/10000000000 : ℝ), (2559084119/5000000000 : ℝ), (1600407597/10000000000 : ℝ)] ![(8906340373473/20000000000000 : ℝ), (44531859382041/100000000000000 : ℝ), (5468219370297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5118153249/10000000000 : ℝ)|^93 ≤ (8906340373473/20000000000000 : ℝ)^77
        have hw : |(5118153249/10000000000 : ℝ)|=(5118153249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2559084119/5000000000 : ℝ)|^93 ≤ (44531859382041/100000000000000 : ℝ)^77
        have hw : |(2559084119/5000000000 : ℝ)|=(2559084119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1600407597/10000000000 : ℝ)|^93 ≤ (5468219370297/50000000000000 : ℝ)^77
        have hw : |(1600407597/10000000000 : ℝ)|=(1600407597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328056_s1_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5118153249/10000000000 : ℝ)*x 0 + (2559084119/5000000000 : ℝ)*x 1 + (-1600407597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5118153249/10000000000 : ℝ)^93 ≤ (8906340373473/20000000000000 : ℝ)^77 := by
    have hnat : (5118153249 : ℕ)^93*20000000000000^77 ≤ 8906340373473^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5118153249 10000000000 8906340373473 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2559084119/5000000000 : ℝ)^93 ≤ (44531859382041/100000000000000 : ℝ)^77 := by
    have hnat : (2559084119 : ℕ)^93*100000000000000^77 ≤ 44531859382041^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559084119 5000000000 44531859382041 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1600407597/10000000000 : ℝ)^93 ≤ (5468219370297/50000000000000 : ℝ)^77 := by
    have hnat : (1600407597 : ℕ)^93*50000000000000^77 ≤ 5468219370297^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600407597 10000000000 5468219370297 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5118153249/10000000000 : ℝ), (2559084119/5000000000 : ℝ), (-1600407597/10000000000 : ℝ)] ![(8906340373473/20000000000000 : ℝ), (44531859382041/100000000000000 : ℝ), (5468219370297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5118153249/10000000000 : ℝ)|^93 ≤ (8906340373473/20000000000000 : ℝ)^77
        have hw : |(5118153249/10000000000 : ℝ)|=(5118153249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2559084119/5000000000 : ℝ)|^93 ≤ (44531859382041/100000000000000 : ℝ)^77
        have hw : |(2559084119/5000000000 : ℝ)|=(2559084119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1600407597/10000000000 : ℝ)|^93 ≤ (5468219370297/50000000000000 : ℝ)^77
        have hw : |(-1600407597/10000000000 : ℝ)|=(1600407597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328056 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (80697/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-116026531/400000000 : ℝ)*X 0 0+(11602653/40000000 : ℝ)*X 0 1+(-6108852343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((116026531/400000000 : ℝ)*X 1 0+(-2900663249/10000000000 : ℝ)*X 1 1+(-6108852343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-280873027/1250000000 : ℝ)*X 0 0+(606411893/5000000000 : ℝ)*X 0 1+(-1985339033/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1123491999/5000000000 : ℝ)*X 1 0+(-303205917/2500000000 : ℝ)*X 1 1+(-7941356381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3337620731/10000000000 : ℝ)*X 2 0+(7380177367/10000000000 : ℝ)*X 2 1+(17907239/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-303205917/2500000000 : ℝ)*X 0 0+(1123491999/5000000000 : ℝ)*X 0 1+(-7941356381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((606411893/5000000000 : ℝ)*X 1 0+(-280873027/1250000000 : ℝ)*X 1 1+(-1985339033/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((7380177367/10000000000 : ℝ)*X 2 0+(3337620731/10000000000 : ℝ)*X 2 1+(17907239/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((-2062024529/5000000000 : ℝ)*X 0 0+(1931293829/10000000000 : ℝ)*X 0 1+(-5816342813/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s0_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((965646677/5000000000 : ℝ)*X 1 0+(-412404911/1000000000 : ℝ)*X 1 1+(-2908171571/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s0_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((5411661311/10000000000 : ℝ)*X 2 0+(5411661211/10000000000 : ℝ)*X 2 1+(399885079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s0_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((14893/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14893/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1337139622403139/78125000000000000000 : ℝ) := by norm_num
    linear_combination (1992605452493/1000000000000 : ℝ)*(base5) + (121202522703/100000000000 : ℝ)*(base7) + (778763/1000000000000 : ℝ)*(base50) + (350885346457/200000000000 : ℝ)*(base59) + (439211288371/1000000000000 : ℝ)*(base60) + (846831972099/500000000000 : ℝ)*(major_s0_0) + (846831972099/500000000000 : ℝ)*(major_s0_1) + (846831972099/500000000000 : ℝ)*(major_s0_2) + (591699/250000000000 : ℝ)*(sp_s0_0) + (688211/100000000000 : ℝ)*(sp_s0_1) + (312740419/160000000 : ℝ)*(sp_s0_7) + (977344872027/500000000000 : ℝ)*(sp_s0_8) + (3947302078657/1000000000000 : ℝ)*(sp_s0_9) + (33320309/500000000000 : ℝ)*(sp_s0_13) + (780580225463/1000000000000 : ℝ)*(f.failure) + (488674156541/250000000000 : ℝ)*(f.sum) + (1478203431/2500000000000000000000 : ℝ)*base63 + (17658250800983/100000000000000000000000000 : ℝ)*base64 + (652786979017/100000000000000000000000000 : ℝ)*base66 + (2737204522648231/5000000000000000000000000000 : ℝ)*base69 + (1469740770697381/5000000000000000000000000000 : ℝ)*base70 + (10739521200983/100000000000000000000000000 : ℝ)*base73 + (872297272851769/5000000000000000000000000000 : ℝ)*base75 + (147638346851769/5000000000000000000000000000 : ℝ)*base77 + (3680006439017/50000000000000000000000000 : ℝ)*base78 + (1377/4000000000000000 : ℝ)*base87 + (1377/4000000000000000 : ℝ)*base89 + (1377/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14893/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14893/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (42788473729620102739593/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1992605452493/1000000000000 : ℝ)*(base5) + (121202522703/100000000000 : ℝ)*(base7) + (778763/1000000000000 : ℝ)*(base40) + (350885346457/200000000000 : ℝ)*(base59) + (1237071394787/1000000000000 : ℝ)*(base60) + (846831972099/500000000000 : ℝ)*(major_s0_0) + (846831972099/500000000000 : ℝ)*(major_s0_1) + (846831972099/500000000000 : ℝ)*(major_s0_2) + (688211/100000000000 : ℝ)*(sp_s0_0) + (591699/250000000000 : ℝ)*(sp_s0_1) + (33320309/500000000000 : ℝ)*(sp_s0_8) + (977344872027/500000000000 : ℝ)*(sp_s0_13) + (312740419/160000000 : ℝ)*(sp_s0_14) + (3947302078657/1000000000000 : ℝ)*(sp_s0_15) + (780580225463/1000000000000 : ℝ)*(f.failure) + (488674156541/250000000000 : ℝ)*(f.sum) + (357509839/5000000000000000000000 : ℝ)*base62 + (36009347919017/100000000000000000000000000 : ℝ)*base65 + (10739521200983/100000000000000000000000000 : ℝ)*base67 + (110266011648231/5000000000000000000000000000 : ℝ)*base69 + (1902875012302619/5000000000000000000000000000 : ℝ)*base71 + (652786979017/100000000000000000000000000 : ℝ)*base72 + (147638346851769/5000000000000000000000000000 : ℝ)*base75 + (872297272851769/5000000000000000000000000000 : ℝ)*base77 + (3680006439017/50000000000000000000000000 : ℝ)*base78 + (1377/4000000000000000 : ℝ)*base87 + (1377/4000000000000000 : ℝ)*base89 + (1377/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-13579/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-13579/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1922594183893007472201/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1096463217543/1000000000000 : ℝ)*(base5) + (318980754981/1000000000000 : ℝ)*(base7) + (352703/100000000000 : ℝ)*(base8) + (11661/100000000000 : ℝ)*(base15) + (709093/200000000000 : ℝ)*(base16) + (1229/1000000000000 : ℝ)*(base49) + (269458476697/250000000000 : ℝ)*(base59) + (210867821643/125000000000 : ℝ)*(major_s0_0) + (210867821643/125000000000 : ℝ)*(major_s0_1) + (210867821643/125000000000 : ℝ)*(major_s0_2) + (17421/200000000000 : ℝ)*(sp_s0_9) + (1212396432373/500000000000 : ℝ)*(sp_s0_19) + (2424792729701/1000000000000 : ℝ)*(sp_s0_20) + (1760629761107/500000000000 : ℝ)*(sp_s0_21) + (388741231281/500000000000 : ℝ)*(f.failure) + (75774887243/31250000000 : ℝ)*(f.sum) + (215677317/2500000000000000000000 : ℝ)*base63 + (842505334969/25000000000000000000000000 : ℝ)*base65 + (3899289825031/25000000000000000000000000 : ℝ)*base67 + (60791743672833/1250000000000000000000000000 : ℝ)*base68 + (396912815828717/1250000000000000000000000000 : ℝ)*base70 + (881514935031/25000000000000000000000000 : ℝ)*base73 + (265498810797833/1250000000000000000000000000 : ℝ)*base75 + (147554138297833/1250000000000000000000000000 : ℝ)*base77 + (3082096565031/12500000000000000000000000 : ℝ)*base79 + (201/2000000000000000 : ℝ)*base86 + (201/2000000000000000 : ℝ)*base88 + (201/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (14893/25000 : ℝ) ^ (91/16 : ℝ) ≤ (5254754169880744493/100000000000000000000 : ℝ) := by
    have hpowers : (14893/25000 : ℝ)^91 ≤ (5254754169880744493/100000000000000000000 : ℝ)^16 := by
      have hnat : (14893 : ℕ)^91*100000000000000000000^16 ≤ 5254754169880744493^16*25000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14893 25000 5254754169880744493 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14893/25000 : ℝ)) (X := (5254754169880744493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (105254754169880744493/100000000000000000000 : ℝ) ≤ (10090452267023719/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (105254754169880744493/100000000000000000000 : ℝ)^16 ≤ (10090452267023719/10000000000000000 : ℝ)^91 := by
      have hnat : (105254754169880744493 : ℕ)^16*10000000000000000^91 ≤ 10090452267023719^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105254754169880744493 100000000000000000000 10090452267023719 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10090452267023719/10000000000000000 : ℝ)) (X := (105254754169880744493/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (55254754169880744493/50000000000000000000 : ℝ) ≤ (10177256191286857/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (55254754169880744493/50000000000000000000 : ℝ)^16 ≤ (10177256191286857/10000000000000000 : ℝ)^91 := by
      have hnat : (55254754169880744493 : ℕ)^16*10000000000000000^91 ≤ 10177256191286857^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55254754169880744493 50000000000000000000 10177256191286857 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10177256191286857/10000000000000000 : ℝ)) (X := (55254754169880744493/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(90452267023719/5957200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(43401962131569/2978600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (14893/25000 : ℝ)) (alpha := (90452267023719/5957200000000000 : ℝ)) (beta := (43401962131569/2978600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (14893/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(90452267023719/5957200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(43401962131569/2978600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (14893/25000 : ℝ) ^ (91/16 : ℝ) ≤ (5254754169880744493/100000000000000000000 : ℝ) := by
    have hpowers : (14893/25000 : ℝ)^91 ≤ (5254754169880744493/100000000000000000000 : ℝ)^16 := by
      have hnat : (14893 : ℕ)^91*100000000000000000000^16 ≤ 5254754169880744493^16*25000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14893 25000 5254754169880744493 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14893/25000 : ℝ)) (X := (5254754169880744493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (105254754169880744493/100000000000000000000 : ℝ) ≤ (10090452267023719/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (105254754169880744493/100000000000000000000 : ℝ)^16 ≤ (10090452267023719/10000000000000000 : ℝ)^91 := by
      have hnat : (105254754169880744493 : ℕ)^16*10000000000000000^91 ≤ 10090452267023719^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105254754169880744493 100000000000000000000 10090452267023719 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10090452267023719/10000000000000000 : ℝ)) (X := (105254754169880744493/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (55254754169880744493/50000000000000000000 : ℝ) ≤ (10177256191286857/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (55254754169880744493/50000000000000000000 : ℝ)^16 ≤ (10177256191286857/10000000000000000 : ℝ)^91 := by
      have hnat : (55254754169880744493 : ℕ)^16*10000000000000000^91 ≤ 10177256191286857^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55254754169880744493 50000000000000000000 10177256191286857 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10177256191286857/10000000000000000 : ℝ)) (X := (55254754169880744493/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(90452267023719/5957200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(43401962131569/2978600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (14893/25000 : ℝ)) (alpha := (90452267023719/5957200000000000 : ℝ)) (beta := (43401962131569/2978600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (14893/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(90452267023719/5957200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(43401962131569/2978600000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13579/100000 : ℝ) ^ (91/16 : ℝ) ≤ (1169999149546947/100000000000000000000 : ℝ) := by
    have hpowers : (13579/100000 : ℝ)^91 ≤ (1169999149546947/100000000000000000000 : ℝ)^16 := by
      have hnat : (13579 : ℕ)^91*100000000000000000000^16 ≤ 1169999149546947^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13579 100000 1169999149546947 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13579/100000 : ℝ)) (X := (1169999149546947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100001169999149546947/100000000000000000000 : ℝ) ≤ (2500005142828609/2500000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (100001169999149546947/100000000000000000000 : ℝ)^16 ≤ (2500005142828609/2500000000000000 : ℝ)^91 := by
      have hnat : (100001169999149546947 : ℕ)^16*2500000000000000^91 ≤ 2500005142828609^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100001169999149546947 100000000000000000000 2500005142828609 2500000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500005142828609/2500000000000000 : ℝ)) (X := (100001169999149546947/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50001169999149546947/50000000000000000000 : ℝ) ≤ (10000041142430509/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (50001169999149546947/50000000000000000000 : ℝ)^16 ≤ (10000041142430509/10000000000000000 : ℝ)^91 := by
      have hnat : (50001169999149546947 : ℕ)^16*10000000000000000^91 ≤ 10000041142430509^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001169999149546947 50000000000000000000 10000041142430509 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000041142430509/10000000000000000 : ℝ)) (X := (50001169999149546947/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(5142828609/339475000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(20571116073/1357900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (13579/100000 : ℝ)) (alpha := (5142828609/339475000000000 : ℝ)) (beta := (20571116073/1357900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (13579/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(5142828609/339475000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(20571116073/1357900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3233966383/10000000000 : ℝ)*X 0 0+(1616989717/5000000000 : ℝ)*X 0 1+(-2762624293/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3233966383/10000000000 : ℝ)*X 1 0+(-1616989717/5000000000 : ℝ)*X 1 1+(-2762624293/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5118153249/10000000000 : ℝ)*X 2 0+(2559084119/5000000000 : ℝ)*X 2 1+(1600407597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5118153249/10000000000 : ℝ)*X 0 0+(2559084119/5000000000 : ℝ)*X 0 1+(-1600407597/10000000000 : ℝ)*X 0 2+(5118153249/10000000000 : ℝ)*X 1 0+(2559084119/5000000000 : ℝ)*X 1 1+(-1600407597/10000000000 : ℝ)*X 1 2+(5118153249/10000000000 : ℝ)*X 2 0+(2559084119/5000000000 : ℝ)*X 2 1+(-1600407597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328056_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-20037/2000 : ℝ) < ((-8679/4000 : ℝ)*P 0+(-8679/4000 : ℝ)*P 1+(-8679/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-20037/2000 : ℝ) < (-200433324525808819279280101008627/20223204700000000000000000000000 : ℝ) := by norm_num
    linear_combination (7574429/1000000000000 : ℝ)*(base12) + (36683/200000000000 : ℝ)*(base25) + (7537021/1000000000000 : ℝ)*(base33) + (76364576503/500000000000 : ℝ)*(base39) + (152722461221/1000000000000 : ℝ)*(base49) + (971799/1000000000000 : ℝ)*(base50) + (589496789249/500000000000 : ℝ)*(base59) + (147373979949/250000000000 : ℝ)*(base60) + (2169742462979/1000000000000 : ℝ)*(major_s1_0) + (8679/4000 : ℝ)*(major_s1_1) + (8679/4000 : ℝ)*(major_s1_2) + (41295974097/12500000000 : ℝ)*(sp_s1_0) + (206479872823/62500000000 : ℝ)*(sp_s1_1) + (412959722719/125000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (3303685502189/1000000000000 : ℝ)*(f.sum) + (3821374233963/98746116699218750000000000 : ℝ)*base62 + (42053738621/848687500000000000000000 : ℝ)*base64 + (64143175207/232703125000000000000000 : ℝ)*base67 + (3682419500989/8486875000000000000000000 : ℝ)*base69 + (9925571339084728761/80892818800000000000000000000000 : ℝ)*base70 + (640349243845331/2978600000000000000000000000 : ℝ)*base73 + (11286846967567/18616250000000000000000000 : ℝ)*base75 + (1208165728736181/5957200000000000000000000000 : ℝ)*base77 + (2888676444164211/2978600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p028_b026 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 56 ≤ c.val) (hhi : c.val < 57)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=56 := by omega
  rcases hc with rfl
  · exact collision_c328056 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 56 ≤ c.val) (hhi : c.val < 57)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b026 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
