-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_positive87
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:04:02.971004+00:00
-- url     : https://prove2.me/submissions/dca99fb3-2a8a-40f1-bf14-ce08726d2da5

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
theorem collision_support_c325087_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-37055427/2000000000 : ℝ)*x 0 + (685363481/1250000000 : ℝ)*x 1 + (1161131381/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37055427/2000000000 : ℝ)^87 ≤ (94271806311/12500000000000 : ℝ)^71 := by
    have hnat : (37055427 : ℕ)^87*12500000000000^71 ≤ 94271806311^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37055427 2000000000 94271806311 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685363481/1250000000 : ℝ)^87 ≤ (47884671471827/100000000000000 : ℝ)^71 := by
    have hnat : (685363481 : ℕ)^87*100000000000000^71 ≤ 47884671471827^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685363481 1250000000 47884671471827 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161131381/2000000000 : ℝ)^87 ≤ (25680577027931/50000000000000 : ℝ)^71 := by
    have hnat : (1161131381 : ℕ)^87*50000000000000^71 ≤ 25680577027931^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161131381 2000000000 25680577027931 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37055427/2000000000 : ℝ), (685363481/1250000000 : ℝ), (1161131381/2000000000 : ℝ)] ![(94271806311/12500000000000 : ℝ), (47884671471827/100000000000000 : ℝ), (25680577027931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37055427/2000000000 : ℝ)|^87 ≤ (94271806311/12500000000000 : ℝ)^71
        have hw : |(-37055427/2000000000 : ℝ)|=(37055427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685363481/1250000000 : ℝ)|^87 ≤ (47884671471827/100000000000000 : ℝ)^71
        have hw : |(685363481/1250000000 : ℝ)|=(685363481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1161131381/2000000000 : ℝ)|^87 ≤ (25680577027931/50000000000000 : ℝ)^71
        have hw : |(1161131381/2000000000 : ℝ)|=(1161131381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2902828453/5000000000 : ℝ)*x 0 + (-37055427/2000000000 : ℝ)*x 1 + (685363481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2902828453/5000000000 : ℝ)^87 ≤ (51361154066703/100000000000000 : ℝ)^71 := by
    have hnat : (2902828453 : ℕ)^87*100000000000000^71 ≤ 51361154066703^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2902828453 5000000000 51361154066703 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37055427/2000000000 : ℝ)^87 ≤ (94271806311/12500000000000 : ℝ)^71 := by
    have hnat : (37055427 : ℕ)^87*12500000000000^71 ≤ 94271806311^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37055427 2000000000 94271806311 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685363481/1250000000 : ℝ)^87 ≤ (47884671471827/100000000000000 : ℝ)^71 := by
    have hnat : (685363481 : ℕ)^87*100000000000000^71 ≤ 47884671471827^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685363481 1250000000 47884671471827 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2902828453/5000000000 : ℝ), (-37055427/2000000000 : ℝ), (685363481/1250000000 : ℝ)] ![(51361154066703/100000000000000 : ℝ), (94271806311/12500000000000 : ℝ), (47884671471827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2902828453/5000000000 : ℝ)|^87 ≤ (51361154066703/100000000000000 : ℝ)^71
        have hw : |(2902828453/5000000000 : ℝ)|=(2902828453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37055427/2000000000 : ℝ)|^87 ≤ (94271806311/12500000000000 : ℝ)^71
        have hw : |(-37055427/2000000000 : ℝ)|=(37055427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685363481/1250000000 : ℝ)|^87 ≤ (47884671471827/100000000000000 : ℝ)^71
        have hw : |(685363481/1250000000 : ℝ)|=(685363481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (685363481/1250000000 : ℝ)*x 0 + (2902828453/5000000000 : ℝ)*x 1 + (-37055427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685363481/1250000000 : ℝ)^87 ≤ (47884671471827/100000000000000 : ℝ)^71 := by
    have hnat : (685363481 : ℕ)^87*100000000000000^71 ≤ 47884671471827^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685363481 1250000000 47884671471827 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2902828453/5000000000 : ℝ)^87 ≤ (51361154066703/100000000000000 : ℝ)^71 := by
    have hnat : (2902828453 : ℕ)^87*100000000000000^71 ≤ 51361154066703^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2902828453 5000000000 51361154066703 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37055427/2000000000 : ℝ)^87 ≤ (94271806311/12500000000000 : ℝ)^71 := by
    have hnat : (37055427 : ℕ)^87*12500000000000^71 ≤ 94271806311^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37055427 2000000000 94271806311 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685363481/1250000000 : ℝ), (2902828453/5000000000 : ℝ), (-37055427/2000000000 : ℝ)] ![(47884671471827/100000000000000 : ℝ), (51361154066703/100000000000000 : ℝ), (94271806311/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685363481/1250000000 : ℝ)|^87 ≤ (47884671471827/100000000000000 : ℝ)^71
        have hw : |(685363481/1250000000 : ℝ)|=(685363481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2902828453/5000000000 : ℝ)|^87 ≤ (51361154066703/100000000000000 : ℝ)^71
        have hw : |(2902828453/5000000000 : ℝ)|=(2902828453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37055427/2000000000 : ℝ)|^87 ≤ (94271806311/12500000000000 : ℝ)^71
        have hw : |(-37055427/2000000000 : ℝ)|=(37055427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-11004873/80000000 : ℝ)*x 0 + (19553917/200000000 : ℝ)*x 1 + (2198151547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11004873/80000000 : ℝ)^87 ≤ (8797374640547/100000000000000 : ℝ)^71 := by
    have hnat : (11004873 : ℕ)^87*100000000000000^71 ≤ 8797374640547^71*80000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11004873 80000000 8797374640547 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19553917/200000000 : ℝ)^87 ≤ (578953999359/10000000000000 : ℝ)^71 := by
    have hnat : (19553917 : ℕ)^87*10000000000000^71 ≤ 578953999359^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19553917 200000000 578953999359 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198151547/2500000000 : ℝ)^87 ≤ (85413085349811/100000000000000 : ℝ)^71 := by
    have hnat : (2198151547 : ℕ)^87*100000000000000^71 ≤ 85413085349811^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198151547 2500000000 85413085349811 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11004873/80000000 : ℝ), (19553917/200000000 : ℝ), (2198151547/2500000000 : ℝ)] ![(8797374640547/100000000000000 : ℝ), (578953999359/10000000000000 : ℝ), (85413085349811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11004873/80000000 : ℝ)|^87 ≤ (8797374640547/100000000000000 : ℝ)^71
        have hw : |(-11004873/80000000 : ℝ)|=(11004873/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19553917/200000000 : ℝ)|^87 ≤ (578953999359/10000000000000 : ℝ)^71
        have hw : |(19553917/200000000 : ℝ)|=(19553917/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2198151547/2500000000 : ℝ)|^87 ≤ (85413085349811/100000000000000 : ℝ)^71
        have hw : |(2198151547/2500000000 : ℝ)|=(2198151547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (164071343/400000000 : ℝ)*x 0 + (-17337903/625000000 : ℝ)*x 1 + (7054314131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164071343/400000000 : ℝ)^87 ≤ (16777426144429/50000000000000 : ℝ)^71 := by
    have hnat : (164071343 : ℕ)^87*50000000000000^71 ≤ 16777426144429^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164071343 400000000 16777426144429 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17337903/625000000 : ℝ)^87 ≤ (1236714854491/100000000000000 : ℝ)^71 := by
    have hnat : (17337903 : ℕ)^87*100000000000000^71 ≤ 1236714854491^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17337903 625000000 1236714854491 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7054314131/10000000000 : ℝ)^87 ≤ (2037763526457/3125000000000 : ℝ)^71 := by
    have hnat : (7054314131 : ℕ)^87*3125000000000^71 ≤ 2037763526457^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7054314131 10000000000 2037763526457 3125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164071343/400000000 : ℝ), (-17337903/625000000 : ℝ), (7054314131/10000000000 : ℝ)] ![(16777426144429/50000000000000 : ℝ), (1236714854491/100000000000000 : ℝ), (2037763526457/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164071343/400000000 : ℝ)|^87 ≤ (16777426144429/50000000000000 : ℝ)^71
        have hw : |(164071343/400000000 : ℝ)|=(164071343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17337903/625000000 : ℝ)|^87 ≤ (1236714854491/100000000000000 : ℝ)^71
        have hw : |(-17337903/625000000 : ℝ)|=(17337903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7054314131/10000000000 : ℝ)|^87 ≤ (2037763526457/3125000000000 : ℝ)^71
        have hw : |(7054314131/10000000000 : ℝ)|=(7054314131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (212010273/1000000000 : ℝ)*x 0 + (876189797/1000000000 : ℝ)*x 1 + (-413687/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212010273/1000000000 : ℝ)^87 ≤ (14946861513019/100000000000000 : ℝ)^71 := by
    have hnat : (212010273 : ℕ)^87*100000000000000^71 ≤ 14946861513019^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212010273 1000000000 14946861513019 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876189797/1000000000 : ℝ)^87 ≤ (85047699928999/100000000000000 : ℝ)^71 := by
    have hnat : (876189797 : ℕ)^87*100000000000000^71 ≤ 85047699928999^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876189797 1000000000 85047699928999 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413687/1250000000 : ℝ)^87 ≤ (5438546463/100000000000000 : ℝ)^71 := by
    have hnat : (413687 : ℕ)^87*100000000000000^71 ≤ 5438546463^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413687 1250000000 5438546463 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212010273/1000000000 : ℝ), (876189797/1000000000 : ℝ), (-413687/1250000000 : ℝ)] ![(14946861513019/100000000000000 : ℝ), (85047699928999/100000000000000 : ℝ), (5438546463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212010273/1000000000 : ℝ)|^87 ≤ (14946861513019/100000000000000 : ℝ)^71
        have hw : |(212010273/1000000000 : ℝ)|=(212010273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(876189797/1000000000 : ℝ)|^87 ≤ (85047699928999/100000000000000 : ℝ)^71
        have hw : |(876189797/1000000000 : ℝ)|=(876189797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413687/1250000000 : ℝ)|^87 ≤ (5438546463/100000000000000 : ℝ)^71
        have hw : |(-413687/1250000000 : ℝ)|=(413687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1977560857/10000000000 : ℝ)*x 0 + (715662291/1000000000 : ℝ)*x 1 + (53571561/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1977560857/10000000000 : ℝ)^87 ≤ (857810288611/6250000000000 : ℝ)^71 := by
    have hnat : (1977560857 : ℕ)^87*6250000000000^71 ≤ 857810288611^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977560857 10000000000 857810288611 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (715662291/1000000000 : ℝ)^87 ≤ (16592289406849/25000000000000 : ℝ)^71 := by
    have hnat : (715662291 : ℕ)^87*25000000000000^71 ≤ 16592289406849^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715662291 1000000000 16592289406849 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53571561/200000000 : ℝ)^87 ≤ (19905877735293/100000000000000 : ℝ)^71 := by
    have hnat : (53571561 : ℕ)^87*100000000000000^71 ≤ 19905877735293^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53571561 200000000 19905877735293 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1977560857/10000000000 : ℝ), (715662291/1000000000 : ℝ), (53571561/200000000 : ℝ)] ![(857810288611/6250000000000 : ℝ), (16592289406849/25000000000000 : ℝ), (19905877735293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1977560857/10000000000 : ℝ)|^87 ≤ (857810288611/6250000000000 : ℝ)^71
        have hw : |(1977560857/10000000000 : ℝ)|=(1977560857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(715662291/1000000000 : ℝ)|^87 ≤ (16592289406849/25000000000000 : ℝ)^71
        have hw : |(715662291/1000000000 : ℝ)|=(715662291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53571561/200000000 : ℝ)|^87 ≤ (19905877735293/100000000000000 : ℝ)^71
        have hw : |(53571561/200000000 : ℝ)|=(53571561/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-413687/1250000000 : ℝ)*x 0 + (212010273/1000000000 : ℝ)*x 1 + (876189797/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413687/1250000000 : ℝ)^87 ≤ (5438546463/100000000000000 : ℝ)^71 := by
    have hnat : (413687 : ℕ)^87*100000000000000^71 ≤ 5438546463^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413687 1250000000 5438546463 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212010273/1000000000 : ℝ)^87 ≤ (14946861513019/100000000000000 : ℝ)^71 := by
    have hnat : (212010273 : ℕ)^87*100000000000000^71 ≤ 14946861513019^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212010273 1000000000 14946861513019 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (876189797/1000000000 : ℝ)^87 ≤ (85047699928999/100000000000000 : ℝ)^71 := by
    have hnat : (876189797 : ℕ)^87*100000000000000^71 ≤ 85047699928999^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876189797 1000000000 85047699928999 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413687/1250000000 : ℝ), (212010273/1000000000 : ℝ), (876189797/1000000000 : ℝ)] ![(5438546463/100000000000000 : ℝ), (14946861513019/100000000000000 : ℝ), (85047699928999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413687/1250000000 : ℝ)|^87 ≤ (5438546463/100000000000000 : ℝ)^71
        have hw : |(-413687/1250000000 : ℝ)|=(413687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212010273/1000000000 : ℝ)|^87 ≤ (14946861513019/100000000000000 : ℝ)^71
        have hw : |(212010273/1000000000 : ℝ)|=(212010273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(876189797/1000000000 : ℝ)|^87 ≤ (85047699928999/100000000000000 : ℝ)^71
        have hw : |(876189797/1000000000 : ℝ)|=(876189797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2198151547/2500000000 : ℝ)*x 0 + (-11004873/80000000 : ℝ)*x 1 + (19553917/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2198151547/2500000000 : ℝ)^87 ≤ (85413085349811/100000000000000 : ℝ)^71 := by
    have hnat : (2198151547 : ℕ)^87*100000000000000^71 ≤ 85413085349811^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198151547 2500000000 85413085349811 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11004873/80000000 : ℝ)^87 ≤ (8797374640547/100000000000000 : ℝ)^71 := by
    have hnat : (11004873 : ℕ)^87*100000000000000^71 ≤ 8797374640547^71*80000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11004873 80000000 8797374640547 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19553917/200000000 : ℝ)^87 ≤ (578953999359/10000000000000 : ℝ)^71 := by
    have hnat : (19553917 : ℕ)^87*10000000000000^71 ≤ 578953999359^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19553917 200000000 578953999359 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2198151547/2500000000 : ℝ), (-11004873/80000000 : ℝ), (19553917/200000000 : ℝ)] ![(85413085349811/100000000000000 : ℝ), (8797374640547/100000000000000 : ℝ), (578953999359/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2198151547/2500000000 : ℝ)|^87 ≤ (85413085349811/100000000000000 : ℝ)^71
        have hw : |(2198151547/2500000000 : ℝ)|=(2198151547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11004873/80000000 : ℝ)|^87 ≤ (8797374640547/100000000000000 : ℝ)^71
        have hw : |(-11004873/80000000 : ℝ)|=(11004873/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19553917/200000000 : ℝ)|^87 ≤ (578953999359/10000000000000 : ℝ)^71
        have hw : |(19553917/200000000 : ℝ)|=(19553917/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7054314131/10000000000 : ℝ)*x 0 + (164071343/400000000 : ℝ)*x 1 + (-17337903/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7054314131/10000000000 : ℝ)^87 ≤ (2037763526457/3125000000000 : ℝ)^71 := by
    have hnat : (7054314131 : ℕ)^87*3125000000000^71 ≤ 2037763526457^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7054314131 10000000000 2037763526457 3125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164071343/400000000 : ℝ)^87 ≤ (16777426144429/50000000000000 : ℝ)^71 := by
    have hnat : (164071343 : ℕ)^87*50000000000000^71 ≤ 16777426144429^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164071343 400000000 16777426144429 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17337903/625000000 : ℝ)^87 ≤ (1236714854491/100000000000000 : ℝ)^71 := by
    have hnat : (17337903 : ℕ)^87*100000000000000^71 ≤ 1236714854491^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17337903 625000000 1236714854491 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7054314131/10000000000 : ℝ), (164071343/400000000 : ℝ), (-17337903/625000000 : ℝ)] ![(2037763526457/3125000000000 : ℝ), (16777426144429/50000000000000 : ℝ), (1236714854491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7054314131/10000000000 : ℝ)|^87 ≤ (2037763526457/3125000000000 : ℝ)^71
        have hw : |(7054314131/10000000000 : ℝ)|=(7054314131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164071343/400000000 : ℝ)|^87 ≤ (16777426144429/50000000000000 : ℝ)^71
        have hw : |(164071343/400000000 : ℝ)|=(164071343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17337903/625000000 : ℝ)|^87 ≤ (1236714854491/100000000000000 : ℝ)^71
        have hw : |(-17337903/625000000 : ℝ)|=(17337903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53571561/200000000 : ℝ)*x 0 + (1977560857/10000000000 : ℝ)*x 1 + (715662291/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53571561/200000000 : ℝ)^87 ≤ (19905877735293/100000000000000 : ℝ)^71 := by
    have hnat : (53571561 : ℕ)^87*100000000000000^71 ≤ 19905877735293^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53571561 200000000 19905877735293 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1977560857/10000000000 : ℝ)^87 ≤ (857810288611/6250000000000 : ℝ)^71 := by
    have hnat : (1977560857 : ℕ)^87*6250000000000^71 ≤ 857810288611^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977560857 10000000000 857810288611 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (715662291/1000000000 : ℝ)^87 ≤ (16592289406849/25000000000000 : ℝ)^71 := by
    have hnat : (715662291 : ℕ)^87*25000000000000^71 ≤ 16592289406849^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715662291 1000000000 16592289406849 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53571561/200000000 : ℝ), (1977560857/10000000000 : ℝ), (715662291/1000000000 : ℝ)] ![(19905877735293/100000000000000 : ℝ), (857810288611/6250000000000 : ℝ), (16592289406849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53571561/200000000 : ℝ)|^87 ≤ (19905877735293/100000000000000 : ℝ)^71
        have hw : |(53571561/200000000 : ℝ)|=(53571561/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1977560857/10000000000 : ℝ)|^87 ≤ (857810288611/6250000000000 : ℝ)^71
        have hw : |(1977560857/10000000000 : ℝ)|=(1977560857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(715662291/1000000000 : ℝ)|^87 ≤ (16592289406849/25000000000000 : ℝ)^71
        have hw : |(715662291/1000000000 : ℝ)|=(715662291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-17337903/625000000 : ℝ)*x 0 + (7054314131/10000000000 : ℝ)*x 1 + (164071343/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17337903/625000000 : ℝ)^87 ≤ (1236714854491/100000000000000 : ℝ)^71 := by
    have hnat : (17337903 : ℕ)^87*100000000000000^71 ≤ 1236714854491^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17337903 625000000 1236714854491 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7054314131/10000000000 : ℝ)^87 ≤ (2037763526457/3125000000000 : ℝ)^71 := by
    have hnat : (7054314131 : ℕ)^87*3125000000000^71 ≤ 2037763526457^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7054314131 10000000000 2037763526457 3125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164071343/400000000 : ℝ)^87 ≤ (16777426144429/50000000000000 : ℝ)^71 := by
    have hnat : (164071343 : ℕ)^87*50000000000000^71 ≤ 16777426144429^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164071343 400000000 16777426144429 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17337903/625000000 : ℝ), (7054314131/10000000000 : ℝ), (164071343/400000000 : ℝ)] ![(1236714854491/100000000000000 : ℝ), (2037763526457/3125000000000 : ℝ), (16777426144429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17337903/625000000 : ℝ)|^87 ≤ (1236714854491/100000000000000 : ℝ)^71
        have hw : |(-17337903/625000000 : ℝ)|=(17337903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7054314131/10000000000 : ℝ)|^87 ≤ (2037763526457/3125000000000 : ℝ)^71
        have hw : |(7054314131/10000000000 : ℝ)|=(7054314131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164071343/400000000 : ℝ)|^87 ≤ (16777426144429/50000000000000 : ℝ)^71
        have hw : |(164071343/400000000 : ℝ)|=(164071343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (876189797/1000000000 : ℝ)*x 0 + (-413687/1250000000 : ℝ)*x 1 + (212010273/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (876189797/1000000000 : ℝ)^87 ≤ (85047699928999/100000000000000 : ℝ)^71 := by
    have hnat : (876189797 : ℕ)^87*100000000000000^71 ≤ 85047699928999^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876189797 1000000000 85047699928999 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413687/1250000000 : ℝ)^87 ≤ (5438546463/100000000000000 : ℝ)^71 := by
    have hnat : (413687 : ℕ)^87*100000000000000^71 ≤ 5438546463^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413687 1250000000 5438546463 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212010273/1000000000 : ℝ)^87 ≤ (14946861513019/100000000000000 : ℝ)^71 := by
    have hnat : (212010273 : ℕ)^87*100000000000000^71 ≤ 14946861513019^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212010273 1000000000 14946861513019 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(876189797/1000000000 : ℝ), (-413687/1250000000 : ℝ), (212010273/1000000000 : ℝ)] ![(85047699928999/100000000000000 : ℝ), (5438546463/100000000000000 : ℝ), (14946861513019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(876189797/1000000000 : ℝ)|^87 ≤ (85047699928999/100000000000000 : ℝ)^71
        have hw : |(876189797/1000000000 : ℝ)|=(876189797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413687/1250000000 : ℝ)|^87 ≤ (5438546463/100000000000000 : ℝ)^71
        have hw : |(-413687/1250000000 : ℝ)|=(413687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212010273/1000000000 : ℝ)|^87 ≤ (14946861513019/100000000000000 : ℝ)^71
        have hw : |(212010273/1000000000 : ℝ)|=(212010273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (19553917/200000000 : ℝ)*x 0 + (2198151547/2500000000 : ℝ)*x 1 + (-11004873/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19553917/200000000 : ℝ)^87 ≤ (578953999359/10000000000000 : ℝ)^71 := by
    have hnat : (19553917 : ℕ)^87*10000000000000^71 ≤ 578953999359^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19553917 200000000 578953999359 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198151547/2500000000 : ℝ)^87 ≤ (85413085349811/100000000000000 : ℝ)^71 := by
    have hnat : (2198151547 : ℕ)^87*100000000000000^71 ≤ 85413085349811^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198151547 2500000000 85413085349811 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11004873/80000000 : ℝ)^87 ≤ (8797374640547/100000000000000 : ℝ)^71 := by
    have hnat : (11004873 : ℕ)^87*100000000000000^71 ≤ 8797374640547^71*80000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11004873 80000000 8797374640547 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(19553917/200000000 : ℝ), (2198151547/2500000000 : ℝ), (-11004873/80000000 : ℝ)] ![(578953999359/10000000000000 : ℝ), (85413085349811/100000000000000 : ℝ), (8797374640547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(19553917/200000000 : ℝ)|^87 ≤ (578953999359/10000000000000 : ℝ)^71
        have hw : |(19553917/200000000 : ℝ)|=(19553917/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2198151547/2500000000 : ℝ)|^87 ≤ (85413085349811/100000000000000 : ℝ)^71
        have hw : |(2198151547/2500000000 : ℝ)|=(2198151547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11004873/80000000 : ℝ)|^87 ≤ (8797374640547/100000000000000 : ℝ)^71
        have hw : |(-11004873/80000000 : ℝ)|=(11004873/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s0_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (715662291/1000000000 : ℝ)*x 0 + (53571561/200000000 : ℝ)*x 1 + (1977560857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (715662291/1000000000 : ℝ)^87 ≤ (16592289406849/25000000000000 : ℝ)^71 := by
    have hnat : (715662291 : ℕ)^87*25000000000000^71 ≤ 16592289406849^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715662291 1000000000 16592289406849 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53571561/200000000 : ℝ)^87 ≤ (19905877735293/100000000000000 : ℝ)^71 := by
    have hnat : (53571561 : ℕ)^87*100000000000000^71 ≤ 19905877735293^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53571561 200000000 19905877735293 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1977560857/10000000000 : ℝ)^87 ≤ (857810288611/6250000000000 : ℝ)^71 := by
    have hnat : (1977560857 : ℕ)^87*6250000000000^71 ≤ 857810288611^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977560857 10000000000 857810288611 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(715662291/1000000000 : ℝ), (53571561/200000000 : ℝ), (1977560857/10000000000 : ℝ)] ![(16592289406849/25000000000000 : ℝ), (19905877735293/100000000000000 : ℝ), (857810288611/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(715662291/1000000000 : ℝ)|^87 ≤ (16592289406849/25000000000000 : ℝ)^71
        have hw : |(715662291/1000000000 : ℝ)|=(715662291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53571561/200000000 : ℝ)|^87 ≤ (19905877735293/100000000000000 : ℝ)^71
        have hw : |(53571561/200000000 : ℝ)|=(53571561/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1977560857/10000000000 : ℝ)|^87 ≤ (857810288611/6250000000000 : ℝ)^71
        have hw : |(1977560857/10000000000 : ℝ)|=(1977560857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-978904937/10000000000 : ℝ)*x 0 + (5402999223/10000000000 : ℝ)*x 1 + (677012983/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (978904937/10000000000 : ℝ)^87 ≤ (2899157215037/50000000000000 : ℝ)^71 := by
    have hnat : (978904937 : ℕ)^87*50000000000000^71 ≤ 2899157215037^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978904937 10000000000 2899157215037 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402999223/10000000000 : ℝ)^87 ≤ (23515467676049/50000000000000 : ℝ)^71 := by
    have hnat : (5402999223 : ℕ)^87*50000000000000^71 ≤ 23515467676049^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402999223 10000000000 23515467676049 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677012983/1250000000 : ℝ)^87 ≤ (47170750214713/100000000000000 : ℝ)^71 := by
    have hnat : (677012983 : ℕ)^87*100000000000000^71 ≤ 47170750214713^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677012983 1250000000 47170750214713 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-978904937/10000000000 : ℝ), (5402999223/10000000000 : ℝ), (677012983/1250000000 : ℝ)] ![(2899157215037/50000000000000 : ℝ), (23515467676049/50000000000000 : ℝ), (47170750214713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-978904937/10000000000 : ℝ)|^87 ≤ (2899157215037/50000000000000 : ℝ)^71
        have hw : |(-978904937/10000000000 : ℝ)|=(978904937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402999223/10000000000 : ℝ)|^87 ≤ (23515467676049/50000000000000 : ℝ)^71
        have hw : |(5402999223/10000000000 : ℝ)|=(5402999223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677012983/1250000000 : ℝ)|^87 ≤ (47170750214713/100000000000000 : ℝ)^71
        have hw : |(677012983/1250000000 : ℝ)|=(677012983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5416106357/10000000000 : ℝ)*x 0 + (-97890503/1000000000 : ℝ)*x 1 + (675374583/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416106357/10000000000 : ℝ)^87 ≤ (9434155364013/20000000000000 : ℝ)^71 := by
    have hnat : (5416106357 : ℕ)^87*20000000000000^71 ≤ 9434155364013^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416106357 10000000000 9434155364013 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97890503/1000000000 : ℝ)^87 ≤ (1449578776269/25000000000000 : ℝ)^71 := by
    have hnat : (97890503 : ℕ)^87*25000000000000^71 ≤ 1449578776269^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97890503 1000000000 1449578776269 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675374583/1250000000 : ℝ)^87 ≤ (47030908057301/100000000000000 : ℝ)^71 := by
    have hnat : (675374583 : ℕ)^87*100000000000000^71 ≤ 47030908057301^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675374583 1250000000 47030908057301 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416106357/10000000000 : ℝ), (-97890503/1000000000 : ℝ), (675374583/1250000000 : ℝ)] ![(9434155364013/20000000000000 : ℝ), (1449578776269/25000000000000 : ℝ), (47030908057301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416106357/10000000000 : ℝ)|^87 ≤ (9434155364013/20000000000000 : ℝ)^71
        have hw : |(5416106357/10000000000 : ℝ)|=(5416106357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97890503/1000000000 : ℝ)|^87 ≤ (1449578776269/25000000000000 : ℝ)^71
        have hw : |(-97890503/1000000000 : ℝ)|=(97890503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675374583/1250000000 : ℝ)|^87 ≤ (47030908057301/100000000000000 : ℝ)^71
        have hw : |(675374583/1250000000 : ℝ)|=(675374583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5402997841/10000000000 : ℝ)*x 0 + (677013077/1250000000 : ℝ)*x 1 + (-48945293/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402997841/10000000000 : ℝ)^87 ≤ (23515460305707/50000000000000 : ℝ)^71 := by
    have hnat : (5402997841 : ℕ)^87*50000000000000^71 ≤ 23515460305707^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402997841 10000000000 23515460305707 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677013077/1250000000 : ℝ)^87 ≤ (23585379120037/50000000000000 : ℝ)^71 := by
    have hnat : (677013077 : ℕ)^87*50000000000000^71 ≤ 23585379120037^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677013077 1250000000 23585379120037 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48945293/500000000 : ℝ)^87 ≤ (5798321129289/100000000000000 : ℝ)^71 := by
    have hnat : (48945293 : ℕ)^87*100000000000000^71 ≤ 5798321129289^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48945293 500000000 5798321129289 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402997841/10000000000 : ℝ), (677013077/1250000000 : ℝ), (-48945293/500000000 : ℝ)] ![(23515460305707/50000000000000 : ℝ), (23585379120037/50000000000000 : ℝ), (5798321129289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402997841/10000000000 : ℝ)|^87 ≤ (23515460305707/50000000000000 : ℝ)^71
        have hw : |(5402997841/10000000000 : ℝ)|=(5402997841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677013077/1250000000 : ℝ)|^87 ≤ (23585379120037/50000000000000 : ℝ)^71
        have hw : |(677013077/1250000000 : ℝ)|=(677013077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48945293/500000000 : ℝ)|^87 ≤ (5798321129289/100000000000000 : ℝ)^71
        have hw : |(-48945293/500000000 : ℝ)|=(48945293/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-864679797/10000000000 : ℝ)*x 0 + (2225855197/5000000000 : ℝ)*x 1 + (640428261/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864679797/10000000000 : ℝ)^87 ≤ (498050534357/10000000000000 : ℝ)^71 := by
    have hnat : (864679797 : ℕ)^87*10000000000000^71 ≤ 498050534357^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864679797 10000000000 498050534357 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2225855197/5000000000 : ℝ)^87 ≤ (7419108021067/20000000000000 : ℝ)^71 := by
    have hnat : (2225855197 : ℕ)^87*20000000000000^71 ≤ 7419108021067^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225855197 5000000000 7419108021067 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640428261/1000000000 : ℝ)^87 ≤ (57923954540001/100000000000000 : ℝ)^71 := by
    have hnat : (640428261 : ℕ)^87*100000000000000^71 ≤ 57923954540001^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640428261 1000000000 57923954540001 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-864679797/10000000000 : ℝ), (2225855197/5000000000 : ℝ), (640428261/1000000000 : ℝ)] ![(498050534357/10000000000000 : ℝ), (7419108021067/20000000000000 : ℝ), (57923954540001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-864679797/10000000000 : ℝ)|^87 ≤ (498050534357/10000000000000 : ℝ)^71
        have hw : |(-864679797/10000000000 : ℝ)|=(864679797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2225855197/5000000000 : ℝ)|^87 ≤ (7419108021067/20000000000000 : ℝ)^71
        have hw : |(2225855197/5000000000 : ℝ)|=(2225855197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(640428261/1000000000 : ℝ)|^87 ≤ (57923954540001/100000000000000 : ℝ)^71
        have hw : |(640428261/1000000000 : ℝ)|=(640428261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1130794211/2000000000 : ℝ)*x 0 + (-13526267/1000000000 : ℝ)*x 1 + (2829013251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1130794211/2000000000 : ℝ)^87 ≤ (49721696357743/100000000000000 : ℝ)^71 := by
    have hnat : (1130794211 : ℕ)^87*100000000000000^71 ≤ 49721696357743^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130794211 2000000000 49721696357743 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13526267/1000000000 : ℝ)^87 ≤ (256451335089/50000000000000 : ℝ)^71 := by
    have hnat : (13526267 : ℕ)^87*50000000000000^71 ≤ 256451335089^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13526267 1000000000 256451335089 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2829013251/5000000000 : ℝ)^87 ≤ (49765400950901/100000000000000 : ℝ)^71 := by
    have hnat : (2829013251 : ℕ)^87*100000000000000^71 ≤ 49765400950901^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829013251 5000000000 49765400950901 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1130794211/2000000000 : ℝ), (-13526267/1000000000 : ℝ), (2829013251/5000000000 : ℝ)] ![(49721696357743/100000000000000 : ℝ), (256451335089/50000000000000 : ℝ), (49765400950901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1130794211/2000000000 : ℝ)|^87 ≤ (49721696357743/100000000000000 : ℝ)^71
        have hw : |(1130794211/2000000000 : ℝ)|=(1130794211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13526267/1000000000 : ℝ)|^87 ≤ (256451335089/50000000000000 : ℝ)^71
        have hw : |(-13526267/1000000000 : ℝ)|=(13526267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2829013251/5000000000 : ℝ)|^87 ≤ (49765400950901/100000000000000 : ℝ)^71
        have hw : |(2829013251/5000000000 : ℝ)|=(2829013251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (264241197/625000000 : ℝ)*x 0 + (3514020487/5000000000 : ℝ)*x 1 + (-7916529/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264241197/625000000 : ℝ)^87 ≤ (3482298356469/10000000000000 : ℝ)^71 := by
    have hnat : (264241197 : ℕ)^87*10000000000000^71 ≤ 3482298356469^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264241197 625000000 3482298356469 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3514020487/5000000000 : ℝ)^87 ≤ (811387065609/1250000000000 : ℝ)^71 := by
    have hnat : (3514020487 : ℕ)^87*1250000000000^71 ≤ 811387065609^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3514020487 5000000000 811387065609 1250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7916529/1000000000 : ℝ)^87 ≤ (133025588961/50000000000000 : ℝ)^71 := by
    have hnat : (7916529 : ℕ)^87*50000000000000^71 ≤ 133025588961^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7916529 1000000000 133025588961 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264241197/625000000 : ℝ), (3514020487/5000000000 : ℝ), (-7916529/1000000000 : ℝ)] ![(3482298356469/10000000000000 : ℝ), (811387065609/1250000000000 : ℝ), (133025588961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264241197/625000000 : ℝ)|^87 ≤ (3482298356469/10000000000000 : ℝ)^71
        have hw : |(264241197/625000000 : ℝ)|=(264241197/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3514020487/5000000000 : ℝ)|^87 ≤ (811387065609/1250000000000 : ℝ)^71
        have hw : |(3514020487/5000000000 : ℝ)|=(3514020487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7916529/1000000000 : ℝ)|^87 ≤ (133025588961/50000000000000 : ℝ)^71
        have hw : |(-7916529/1000000000 : ℝ)|=(7916529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (353364803/1000000000 : ℝ)*x 0 + (640578343/1250000000 : ℝ)*x 1 + (707071433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353364803/1000000000 : ℝ)^87 ≤ (6988025188849/25000000000000 : ℝ)^71 := by
    have hnat : (353364803 : ℕ)^87*25000000000000^71 ≤ 6988025188849^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353364803 1000000000 6988025188849 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640578343/1250000000 : ℝ)^87 ≤ (44079231157689/100000000000000 : ℝ)^71 := by
    have hnat : (640578343 : ℕ)^87*100000000000000^71 ≤ 44079231157689^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640578343 1250000000 44079231157689 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (707071433/2000000000 : ℝ)^87 ≤ (1118746722771/4000000000000 : ℝ)^71 := by
    have hnat : (707071433 : ℕ)^87*4000000000000^71 ≤ 1118746722771^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707071433 2000000000 1118746722771 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(353364803/1000000000 : ℝ), (640578343/1250000000 : ℝ), (707071433/2000000000 : ℝ)] ![(6988025188849/25000000000000 : ℝ), (44079231157689/100000000000000 : ℝ), (1118746722771/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(353364803/1000000000 : ℝ)|^87 ≤ (6988025188849/25000000000000 : ℝ)^71
        have hw : |(353364803/1000000000 : ℝ)|=(353364803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640578343/1250000000 : ℝ)|^87 ≤ (44079231157689/100000000000000 : ℝ)^71
        have hw : |(640578343/1250000000 : ℝ)|=(640578343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(707071433/2000000000 : ℝ)|^87 ≤ (1118746722771/4000000000000 : ℝ)^71
        have hw : |(707071433/2000000000 : ℝ)|=(707071433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-7916529/1000000000 : ℝ)*x 0 + (264241197/625000000 : ℝ)*x 1 + (3514020487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7916529/1000000000 : ℝ)^87 ≤ (133025588961/50000000000000 : ℝ)^71 := by
    have hnat : (7916529 : ℕ)^87*50000000000000^71 ≤ 133025588961^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7916529 1000000000 133025588961 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264241197/625000000 : ℝ)^87 ≤ (3482298356469/10000000000000 : ℝ)^71 := by
    have hnat : (264241197 : ℕ)^87*10000000000000^71 ≤ 3482298356469^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264241197 625000000 3482298356469 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3514020487/5000000000 : ℝ)^87 ≤ (811387065609/1250000000000 : ℝ)^71 := by
    have hnat : (3514020487 : ℕ)^87*1250000000000^71 ≤ 811387065609^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3514020487 5000000000 811387065609 1250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7916529/1000000000 : ℝ), (264241197/625000000 : ℝ), (3514020487/5000000000 : ℝ)] ![(133025588961/50000000000000 : ℝ), (3482298356469/10000000000000 : ℝ), (811387065609/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7916529/1000000000 : ℝ)|^87 ≤ (133025588961/50000000000000 : ℝ)^71
        have hw : |(-7916529/1000000000 : ℝ)|=(7916529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264241197/625000000 : ℝ)|^87 ≤ (3482298356469/10000000000000 : ℝ)^71
        have hw : |(264241197/625000000 : ℝ)|=(264241197/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3514020487/5000000000 : ℝ)|^87 ≤ (811387065609/1250000000000 : ℝ)^71
        have hw : |(3514020487/5000000000 : ℝ)|=(3514020487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (640428261/1000000000 : ℝ)*x 0 + (-864679797/10000000000 : ℝ)*x 1 + (2225855197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (640428261/1000000000 : ℝ)^87 ≤ (57923954540001/100000000000000 : ℝ)^71 := by
    have hnat : (640428261 : ℕ)^87*100000000000000^71 ≤ 57923954540001^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640428261 1000000000 57923954540001 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (864679797/10000000000 : ℝ)^87 ≤ (498050534357/10000000000000 : ℝ)^71 := by
    have hnat : (864679797 : ℕ)^87*10000000000000^71 ≤ 498050534357^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864679797 10000000000 498050534357 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2225855197/5000000000 : ℝ)^87 ≤ (7419108021067/20000000000000 : ℝ)^71 := by
    have hnat : (2225855197 : ℕ)^87*20000000000000^71 ≤ 7419108021067^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225855197 5000000000 7419108021067 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(640428261/1000000000 : ℝ), (-864679797/10000000000 : ℝ), (2225855197/5000000000 : ℝ)] ![(57923954540001/100000000000000 : ℝ), (498050534357/10000000000000 : ℝ), (7419108021067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(640428261/1000000000 : ℝ)|^87 ≤ (57923954540001/100000000000000 : ℝ)^71
        have hw : |(640428261/1000000000 : ℝ)|=(640428261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-864679797/10000000000 : ℝ)|^87 ≤ (498050534357/10000000000000 : ℝ)^71
        have hw : |(-864679797/10000000000 : ℝ)|=(864679797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2225855197/5000000000 : ℝ)|^87 ≤ (7419108021067/20000000000000 : ℝ)^71
        have hw : |(2225855197/5000000000 : ℝ)|=(2225855197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2829013251/5000000000 : ℝ)*x 0 + (1130794211/2000000000 : ℝ)*x 1 + (-13526267/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2829013251/5000000000 : ℝ)^87 ≤ (49765400950901/100000000000000 : ℝ)^71 := by
    have hnat : (2829013251 : ℕ)^87*100000000000000^71 ≤ 49765400950901^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829013251 5000000000 49765400950901 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130794211/2000000000 : ℝ)^87 ≤ (49721696357743/100000000000000 : ℝ)^71 := by
    have hnat : (1130794211 : ℕ)^87*100000000000000^71 ≤ 49721696357743^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130794211 2000000000 49721696357743 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13526267/1000000000 : ℝ)^87 ≤ (256451335089/50000000000000 : ℝ)^71 := by
    have hnat : (13526267 : ℕ)^87*50000000000000^71 ≤ 256451335089^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13526267 1000000000 256451335089 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2829013251/5000000000 : ℝ), (1130794211/2000000000 : ℝ), (-13526267/1000000000 : ℝ)] ![(49765400950901/100000000000000 : ℝ), (49721696357743/100000000000000 : ℝ), (256451335089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2829013251/5000000000 : ℝ)|^87 ≤ (49765400950901/100000000000000 : ℝ)^71
        have hw : |(2829013251/5000000000 : ℝ)|=(2829013251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130794211/2000000000 : ℝ)|^87 ≤ (49721696357743/100000000000000 : ℝ)^71
        have hw : |(1130794211/2000000000 : ℝ)|=(1130794211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13526267/1000000000 : ℝ)|^87 ≤ (256451335089/50000000000000 : ℝ)^71
        have hw : |(-13526267/1000000000 : ℝ)|=(13526267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (707071433/2000000000 : ℝ)*x 0 + (353364803/1000000000 : ℝ)*x 1 + (640578343/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (707071433/2000000000 : ℝ)^87 ≤ (1118746722771/4000000000000 : ℝ)^71 := by
    have hnat : (707071433 : ℕ)^87*4000000000000^71 ≤ 1118746722771^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707071433 2000000000 1118746722771 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353364803/1000000000 : ℝ)^87 ≤ (6988025188849/25000000000000 : ℝ)^71 := by
    have hnat : (353364803 : ℕ)^87*25000000000000^71 ≤ 6988025188849^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353364803 1000000000 6988025188849 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640578343/1250000000 : ℝ)^87 ≤ (44079231157689/100000000000000 : ℝ)^71 := by
    have hnat : (640578343 : ℕ)^87*100000000000000^71 ≤ 44079231157689^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640578343 1250000000 44079231157689 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(707071433/2000000000 : ℝ), (353364803/1000000000 : ℝ), (640578343/1250000000 : ℝ)] ![(1118746722771/4000000000000 : ℝ), (6988025188849/25000000000000 : ℝ), (44079231157689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(707071433/2000000000 : ℝ)|^87 ≤ (1118746722771/4000000000000 : ℝ)^71
        have hw : |(707071433/2000000000 : ℝ)|=(707071433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(353364803/1000000000 : ℝ)|^87 ≤ (6988025188849/25000000000000 : ℝ)^71
        have hw : |(353364803/1000000000 : ℝ)|=(353364803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(640578343/1250000000 : ℝ)|^87 ≤ (44079231157689/100000000000000 : ℝ)^71
        have hw : |(640578343/1250000000 : ℝ)|=(640578343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-13526267/1000000000 : ℝ)*x 0 + (2829013251/5000000000 : ℝ)*x 1 + (1130794211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13526267/1000000000 : ℝ)^87 ≤ (256451335089/50000000000000 : ℝ)^71 := by
    have hnat : (13526267 : ℕ)^87*50000000000000^71 ≤ 256451335089^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13526267 1000000000 256451335089 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2829013251/5000000000 : ℝ)^87 ≤ (49765400950901/100000000000000 : ℝ)^71 := by
    have hnat : (2829013251 : ℕ)^87*100000000000000^71 ≤ 49765400950901^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829013251 5000000000 49765400950901 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130794211/2000000000 : ℝ)^87 ≤ (49721696357743/100000000000000 : ℝ)^71 := by
    have hnat : (1130794211 : ℕ)^87*100000000000000^71 ≤ 49721696357743^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130794211 2000000000 49721696357743 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13526267/1000000000 : ℝ), (2829013251/5000000000 : ℝ), (1130794211/2000000000 : ℝ)] ![(256451335089/50000000000000 : ℝ), (49765400950901/100000000000000 : ℝ), (49721696357743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13526267/1000000000 : ℝ)|^87 ≤ (256451335089/50000000000000 : ℝ)^71
        have hw : |(-13526267/1000000000 : ℝ)|=(13526267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2829013251/5000000000 : ℝ)|^87 ≤ (49765400950901/100000000000000 : ℝ)^71
        have hw : |(2829013251/5000000000 : ℝ)|=(2829013251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130794211/2000000000 : ℝ)|^87 ≤ (49721696357743/100000000000000 : ℝ)^71
        have hw : |(1130794211/2000000000 : ℝ)|=(1130794211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3514020487/5000000000 : ℝ)*x 0 + (-7916529/1000000000 : ℝ)*x 1 + (264241197/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3514020487/5000000000 : ℝ)^87 ≤ (811387065609/1250000000000 : ℝ)^71 := by
    have hnat : (3514020487 : ℕ)^87*1250000000000^71 ≤ 811387065609^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3514020487 5000000000 811387065609 1250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7916529/1000000000 : ℝ)^87 ≤ (133025588961/50000000000000 : ℝ)^71 := by
    have hnat : (7916529 : ℕ)^87*50000000000000^71 ≤ 133025588961^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7916529 1000000000 133025588961 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264241197/625000000 : ℝ)^87 ≤ (3482298356469/10000000000000 : ℝ)^71 := by
    have hnat : (264241197 : ℕ)^87*10000000000000^71 ≤ 3482298356469^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264241197 625000000 3482298356469 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3514020487/5000000000 : ℝ), (-7916529/1000000000 : ℝ), (264241197/625000000 : ℝ)] ![(811387065609/1250000000000 : ℝ), (133025588961/50000000000000 : ℝ), (3482298356469/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3514020487/5000000000 : ℝ)|^87 ≤ (811387065609/1250000000000 : ℝ)^71
        have hw : |(3514020487/5000000000 : ℝ)|=(3514020487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7916529/1000000000 : ℝ)|^87 ≤ (133025588961/50000000000000 : ℝ)^71
        have hw : |(-7916529/1000000000 : ℝ)|=(7916529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264241197/625000000 : ℝ)|^87 ≤ (3482298356469/10000000000000 : ℝ)^71
        have hw : |(264241197/625000000 : ℝ)|=(264241197/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2225855197/5000000000 : ℝ)*x 0 + (640428261/1000000000 : ℝ)*x 1 + (-864679797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2225855197/5000000000 : ℝ)^87 ≤ (7419108021067/20000000000000 : ℝ)^71 := by
    have hnat : (2225855197 : ℕ)^87*20000000000000^71 ≤ 7419108021067^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225855197 5000000000 7419108021067 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640428261/1000000000 : ℝ)^87 ≤ (57923954540001/100000000000000 : ℝ)^71 := by
    have hnat : (640428261 : ℕ)^87*100000000000000^71 ≤ 57923954540001^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640428261 1000000000 57923954540001 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864679797/10000000000 : ℝ)^87 ≤ (498050534357/10000000000000 : ℝ)^71 := by
    have hnat : (864679797 : ℕ)^87*10000000000000^71 ≤ 498050534357^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864679797 10000000000 498050534357 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2225855197/5000000000 : ℝ), (640428261/1000000000 : ℝ), (-864679797/10000000000 : ℝ)] ![(7419108021067/20000000000000 : ℝ), (57923954540001/100000000000000 : ℝ), (498050534357/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2225855197/5000000000 : ℝ)|^87 ≤ (7419108021067/20000000000000 : ℝ)^71
        have hw : |(2225855197/5000000000 : ℝ)|=(2225855197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640428261/1000000000 : ℝ)|^87 ≤ (57923954540001/100000000000000 : ℝ)^71
        have hw : |(640428261/1000000000 : ℝ)|=(640428261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-864679797/10000000000 : ℝ)|^87 ≤ (498050534357/10000000000000 : ℝ)^71
        have hw : |(-864679797/10000000000 : ℝ)|=(864679797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325087_s1_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (640578343/1250000000 : ℝ)*x 0 + (707071433/2000000000 : ℝ)*x 1 + (353364803/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (640578343/1250000000 : ℝ)^87 ≤ (44079231157689/100000000000000 : ℝ)^71 := by
    have hnat : (640578343 : ℕ)^87*100000000000000^71 ≤ 44079231157689^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640578343 1250000000 44079231157689 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (707071433/2000000000 : ℝ)^87 ≤ (1118746722771/4000000000000 : ℝ)^71 := by
    have hnat : (707071433 : ℕ)^87*4000000000000^71 ≤ 1118746722771^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707071433 2000000000 1118746722771 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353364803/1000000000 : ℝ)^87 ≤ (6988025188849/25000000000000 : ℝ)^71 := by
    have hnat : (353364803 : ℕ)^87*25000000000000^71 ≤ 6988025188849^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353364803 1000000000 6988025188849 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(640578343/1250000000 : ℝ), (707071433/2000000000 : ℝ), (353364803/1000000000 : ℝ)] ![(44079231157689/100000000000000 : ℝ), (1118746722771/4000000000000 : ℝ), (6988025188849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(640578343/1250000000 : ℝ)|^87 ≤ (44079231157689/100000000000000 : ℝ)^71
        have hw : |(640578343/1250000000 : ℝ)|=(640578343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(707071433/2000000000 : ℝ)|^87 ≤ (1118746722771/4000000000000 : ℝ)^71
        have hw : |(707071433/2000000000 : ℝ)|=(707071433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(353364803/1000000000 : ℝ)|^87 ≤ (6988025188849/25000000000000 : ℝ)^71
        have hw : |(353364803/1000000000 : ℝ)|=(353364803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325087 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((37053/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37053/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((37053/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(37053/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37053/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(37053/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (33069/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have s0_pow0 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-37055427/2000000000 : ℝ)*X 0 0+(685363481/1250000000 : ℝ)*X 0 1+(1161131381/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2902828453/5000000000 : ℝ)*X 1 0+(-37055427/2000000000 : ℝ)*X 1 1+(685363481/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((685363481/1250000000 : ℝ)*X 2 0+(2902828453/5000000000 : ℝ)*X 2 1+(-37055427/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-11004873/80000000 : ℝ)*X 0 0+(19553917/200000000 : ℝ)*X 0 1+(2198151547/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((164071343/400000000 : ℝ)*X 1 0+(-17337903/625000000 : ℝ)*X 1 1+(7054314131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((212010273/1000000000 : ℝ)*X 2 0+(876189797/1000000000 : ℝ)*X 2 1+(-413687/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1977560857/10000000000 : ℝ)*X 0 0+(715662291/1000000000 : ℝ)*X 0 1+(53571561/200000000 : ℝ)*X 0 2+(1977560857/10000000000 : ℝ)*X 1 0+(715662291/1000000000 : ℝ)*X 1 1+(53571561/200000000 : ℝ)*X 1 2+(1977560857/10000000000 : ℝ)*X 2 0+(715662291/1000000000 : ℝ)*X 2 1+(53571561/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-413687/1250000000 : ℝ)*X 0 0+(212010273/1000000000 : ℝ)*X 0 1+(876189797/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2198151547/2500000000 : ℝ)*X 1 0+(-11004873/80000000 : ℝ)*X 1 1+(19553917/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7054314131/10000000000 : ℝ)*X 2 0+(164071343/400000000 : ℝ)*X 2 1+(-17337903/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((53571561/200000000 : ℝ)*X 0 0+(1977560857/10000000000 : ℝ)*X 0 1+(715662291/1000000000 : ℝ)*X 0 2+(53571561/200000000 : ℝ)*X 1 0+(1977560857/10000000000 : ℝ)*X 1 1+(715662291/1000000000 : ℝ)*X 1 2+(53571561/200000000 : ℝ)*X 2 0+(1977560857/10000000000 : ℝ)*X 2 1+(715662291/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-17337903/625000000 : ℝ)*X 0 0+(7054314131/10000000000 : ℝ)*X 0 1+(164071343/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((876189797/1000000000 : ℝ)*X 1 0+(-413687/1250000000 : ℝ)*X 1 1+(212010273/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((19553917/200000000 : ℝ)*X 2 0+(2198151547/2500000000 : ℝ)*X 2 1+(-11004873/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((715662291/1000000000 : ℝ)*X 0 0+(53571561/200000000 : ℝ)*X 0 1+(1977560857/10000000000 : ℝ)*X 0 2+(715662291/1000000000 : ℝ)*X 1 0+(53571561/200000000 : ℝ)*X 1 1+(1977560857/10000000000 : ℝ)*X 1 2+(715662291/1000000000 : ℝ)*X 2 0+(53571561/200000000 : ℝ)*X 2 1+(1977560857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((64851/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64851/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (97248511746411299139/12500000000000000000000000 : ℝ) := by norm_num
    linear_combination (232462825277/200000000000 : ℝ)*(base7) + (1603141/500000000000 : ℝ)*(base19) + (89460038779/500000000000 : ℝ)*(base50) + (483017/250000000000 : ℝ)*(base53) + (34441054441/1000000000000 : ℝ)*(base60) + (342076342113/250000000000 : ℝ)*(major_s0_0) + (342076342113/250000000000 : ℝ)*(major_s0_1) + (42759482387/31250000000 : ℝ)*(major_s0_2) + (331467/100000000000 : ℝ)*(sp_s0_0) + (141501847973/100000000000 : ℝ)*(sp_s0_7) + (1415037976803/1000000000000 : ℝ)*(sp_s0_8) + (1415043115153/1000000000000 : ℝ)*(sp_s0_9) + (1843269724079/1000000000000 : ℝ)*(sp_s0_13) + (3877737/200000000000 : ℝ)*(sp_s0_14) + (136191119539/200000000000 : ℝ)*(f.failure) + (1415043115153/1000000000000 : ℝ)*(f.sum) + (1718135044600721/2500000000000000000000000000 : ℝ)*base62 + (102877981750597/312500000000000000000000000 : ℝ)*base65 + (358316591048203/2500000000000000000000000000 : ℝ)*base67 + (224093365313703/312500000000000000000000000 : ℝ)*base68 + (1667612306052979/2500000000000000000000000000 : ℝ)*base71 + (412247954091097/2500000000000000000000000000 : ℝ)*base72 + (1607616516591097/2500000000000000000000000000 : ℝ)*base74 + (207880486451797/2500000000000000000000000000 : ℝ)*base76 + (586996452353553/1250000000000000000000000000 : ℝ)*base79 + (7121/20000000000000000 : ℝ)*base87 + (7121/20000000000000000 : ℝ)*base89 + (7121/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((64851/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(64851/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (97248511758841311639/12500000000000000000000000 : ℝ) := by norm_num
    linear_combination (232462825277/200000000000 : ℝ)*(base7) + (1603141/500000000000 : ℝ)*(base21) + (483017/250000000000 : ℝ)*(base33) + (34441054441/1000000000000 : ℝ)*(base40) + (89460038779/500000000000 : ℝ)*(base60) + (42759482387/31250000000 : ℝ)*(major_s0_0) + (342076342113/250000000000 : ℝ)*(major_s0_1) + (342076342113/250000000000 : ℝ)*(major_s0_2) + (331467/100000000000 : ℝ)*(sp_s0_1) + (1415043115153/1000000000000 : ℝ)*(sp_s0_14) + (141501847973/100000000000 : ℝ)*(sp_s0_15) + (1415037976803/1000000000000 : ℝ)*(sp_s0_16) + (1843269724079/1000000000000 : ℝ)*(sp_s0_20) + (3877737/200000000000 : ℝ)*(sp_s0_22) + (136191119539/200000000000 : ℝ)*(f.failure) + (1415043115153/1000000000000 : ℝ)*(f.sum) + (586996452353553/1250000000000000000000000000 : ℝ)*base63 + (1607616516591097/2500000000000000000000000000 : ℝ)*base64 + (207880486451797/2500000000000000000000000000 : ℝ)*base66 + (357487923548203/2500000000000000000000000000 : ℝ)*base69 + (1718135044600721/2500000000000000000000000000 : ℝ)*base70 + (102877981750597/312500000000000000000000000 : ℝ)*base73 + (412247954091097/2500000000000000000000000000 : ℝ)*base74 + (224093365313703/312500000000000000000000000 : ℝ)*base76 + (1667612306052979/2500000000000000000000000000 : ℝ)*base79 + (7121/20000000000000000 : ℝ)*base87 + (7121/20000000000000000 : ℝ)*base89 + (7121/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64851/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64851/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (97248511758841311639/12500000000000000000000000 : ℝ) := by norm_num
    linear_combination (232462825277/200000000000 : ℝ)*(base7) + (1603141/500000000000 : ℝ)*(base11) + (89460038779/500000000000 : ℝ)*(base40) + (483017/250000000000 : ℝ)*(base43) + (34441054441/1000000000000 : ℝ)*(base50) + (342076342113/250000000000 : ℝ)*(major_s0_0) + (42759482387/31250000000 : ℝ)*(major_s0_1) + (342076342113/250000000000 : ℝ)*(major_s0_2) + (331467/100000000000 : ℝ)*(sp_s0_2) + (3877737/200000000000 : ℝ)*(sp_s0_9) + (1415037976803/1000000000000 : ℝ)*(sp_s0_21) + (1415043115153/1000000000000 : ℝ)*(sp_s0_22) + (141501847973/100000000000 : ℝ)*(sp_s0_23) + (1843269724079/1000000000000 : ℝ)*(sp_s0_27) + (136191119539/200000000000 : ℝ)*(f.failure) + (1415043115153/1000000000000 : ℝ)*(f.sum) + (1667612306052979/2500000000000000000000000000 : ℝ)*base63 + (412247954091097/2500000000000000000000000000 : ℝ)*base64 + (224093365313703/312500000000000000000000000 : ℝ)*base66 + (207880486451797/2500000000000000000000000000 : ℝ)*base68 + (586996452353553/1250000000000000000000000000 : ℝ)*base71 + (1607616516591097/2500000000000000000000000000 : ℝ)*base72 + (102877981750597/312500000000000000000000000 : ℝ)*base75 + (357487923548203/2500000000000000000000000000 : ℝ)*base77 + (1718135044600721/2500000000000000000000000000 : ℝ)*base78 + (7121/20000000000000000 : ℝ)*base87 + (7121/20000000000000000 : ℝ)*base89 + (7121/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (64851/100000 : ℝ) ^ (85/16 : ℝ) ≤ (10018607165297579283/100000000000000000000 : ℝ) := by
    have hpowers : (64851/100000 : ℝ)^85 ≤ (10018607165297579283/100000000000000000000 : ℝ)^16 := by
      have hnat : (64851 : ℕ)^85*100000000000000000000^16 ≤ 10018607165297579283^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64851 100000 10018607165297579283 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64851/100000 : ℝ)) (X := (10018607165297579283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (110018607165297579283/100000000000000000000 : ℝ) ≤ (203627011376841/200000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (110018607165297579283/100000000000000000000 : ℝ)^16 ≤ (203627011376841/200000000000000 : ℝ)^85 := by
      have hnat : (110018607165297579283 : ℕ)^16*200000000000000^85 ≤ 203627011376841^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110018607165297579283 100000000000000000000 203627011376841 200000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (203627011376841/200000000000000 : ℝ)) (X := (110018607165297579283/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (60018607165297579283/50000000000000000000 : ℝ) ≤ (5174877310072997/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (60018607165297579283/50000000000000000000 : ℝ)^16 ≤ (5174877310072997/5000000000000000 : ℝ)^85 := by
      have hnat : (60018607165297579283 : ℕ)^16*5000000000000000^85 ≤ 5174877310072997^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60018607165297579283 50000000000000000000 5174877310072997 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5174877310072997/5000000000000000 : ℝ)) (X := (60018607165297579283/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3627011376841/129702000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(21050506412993/810637500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (64851/100000 : ℝ)) (alpha := (3627011376841/129702000000000 : ℝ)) (beta := (21050506412993/810637500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (64851/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3627011376841/129702000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(21050506412993/810637500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (64851/100000 : ℝ) ^ (85/16 : ℝ) ≤ (10018607165297579283/100000000000000000000 : ℝ) := by
    have hpowers : (64851/100000 : ℝ)^85 ≤ (10018607165297579283/100000000000000000000 : ℝ)^16 := by
      have hnat : (64851 : ℕ)^85*100000000000000000000^16 ≤ 10018607165297579283^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64851 100000 10018607165297579283 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64851/100000 : ℝ)) (X := (10018607165297579283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (110018607165297579283/100000000000000000000 : ℝ) ≤ (203627011376841/200000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (110018607165297579283/100000000000000000000 : ℝ)^16 ≤ (203627011376841/200000000000000 : ℝ)^85 := by
      have hnat : (110018607165297579283 : ℕ)^16*200000000000000^85 ≤ 203627011376841^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110018607165297579283 100000000000000000000 203627011376841 200000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (203627011376841/200000000000000 : ℝ)) (X := (110018607165297579283/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (60018607165297579283/50000000000000000000 : ℝ) ≤ (5174877310072997/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (60018607165297579283/50000000000000000000 : ℝ)^16 ≤ (5174877310072997/5000000000000000 : ℝ)^85 := by
      have hnat : (60018607165297579283 : ℕ)^16*5000000000000000^85 ≤ 5174877310072997^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60018607165297579283 50000000000000000000 5174877310072997 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5174877310072997/5000000000000000 : ℝ)) (X := (60018607165297579283/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(3627011376841/129702000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(21050506412993/810637500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (64851/100000 : ℝ)) (alpha := (3627011376841/129702000000000 : ℝ)) (beta := (21050506412993/810637500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (64851/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(3627011376841/129702000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(21050506412993/810637500000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (64851/100000 : ℝ) ^ (85/16 : ℝ) ≤ (10018607165297579283/100000000000000000000 : ℝ) := by
    have hpowers : (64851/100000 : ℝ)^85 ≤ (10018607165297579283/100000000000000000000 : ℝ)^16 := by
      have hnat : (64851 : ℕ)^85*100000000000000000000^16 ≤ 10018607165297579283^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64851 100000 10018607165297579283 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64851/100000 : ℝ)) (X := (10018607165297579283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (110018607165297579283/100000000000000000000 : ℝ) ≤ (203627011376841/200000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (110018607165297579283/100000000000000000000 : ℝ)^16 ≤ (203627011376841/200000000000000 : ℝ)^85 := by
      have hnat : (110018607165297579283 : ℕ)^16*200000000000000^85 ≤ 203627011376841^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110018607165297579283 100000000000000000000 203627011376841 200000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (203627011376841/200000000000000 : ℝ)) (X := (110018607165297579283/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (60018607165297579283/50000000000000000000 : ℝ) ≤ (5174877310072997/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (60018607165297579283/50000000000000000000 : ℝ)^16 ≤ (5174877310072997/5000000000000000 : ℝ)^85 := by
      have hnat : (60018607165297579283 : ℕ)^16*5000000000000000^85 ≤ 5174877310072997^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60018607165297579283 50000000000000000000 5174877310072997 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5174877310072997/5000000000000000 : ℝ)) (X := (60018607165297579283/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(3627011376841/129702000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(21050506412993/810637500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (64851/100000 : ℝ)) (alpha := (3627011376841/129702000000000 : ℝ)) (beta := (21050506412993/810637500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (64851/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(3627011376841/129702000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(21050506412993/810637500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-978904937/10000000000 : ℝ)*X 0 0+(5402999223/10000000000 : ℝ)*X 0 1+(677012983/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5416106357/10000000000 : ℝ)*X 1 0+(-97890503/1000000000 : ℝ)*X 1 1+(675374583/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5402997841/10000000000 : ℝ)*X 2 0+(677013077/1250000000 : ℝ)*X 2 1+(-48945293/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-864679797/10000000000 : ℝ)*X 0 0+(2225855197/5000000000 : ℝ)*X 0 1+(640428261/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1130794211/2000000000 : ℝ)*X 1 0+(-13526267/1000000000 : ℝ)*X 1 1+(2829013251/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((264241197/625000000 : ℝ)*X 2 0+(3514020487/5000000000 : ℝ)*X 2 1+(-7916529/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((353364803/1000000000 : ℝ)*X 0 0+(640578343/1250000000 : ℝ)*X 0 1+(707071433/2000000000 : ℝ)*X 0 2+(353364803/1000000000 : ℝ)*X 1 0+(640578343/1250000000 : ℝ)*X 1 1+(707071433/2000000000 : ℝ)*X 1 2+(353364803/1000000000 : ℝ)*X 2 0+(640578343/1250000000 : ℝ)*X 2 1+(707071433/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-7916529/1000000000 : ℝ)*X 0 0+(264241197/625000000 : ℝ)*X 0 1+(3514020487/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((640428261/1000000000 : ℝ)*X 1 0+(-864679797/10000000000 : ℝ)*X 1 1+(2225855197/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2829013251/5000000000 : ℝ)*X 2 0+(1130794211/2000000000 : ℝ)*X 2 1+(-13526267/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((707071433/2000000000 : ℝ)*X 0 0+(353364803/1000000000 : ℝ)*X 0 1+(640578343/1250000000 : ℝ)*X 0 2+(707071433/2000000000 : ℝ)*X 1 0+(353364803/1000000000 : ℝ)*X 1 1+(640578343/1250000000 : ℝ)*X 1 2+(707071433/2000000000 : ℝ)*X 2 0+(353364803/1000000000 : ℝ)*X 2 1+(640578343/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-13526267/1000000000 : ℝ)*X 0 0+(2829013251/5000000000 : ℝ)*X 0 1+(1130794211/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3514020487/5000000000 : ℝ)*X 1 0+(-7916529/1000000000 : ℝ)*X 1 1+(264241197/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2225855197/5000000000 : ℝ)*X 2 0+(640428261/1000000000 : ℝ)*X 2 1+(-864679797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((640578343/1250000000 : ℝ)*X 0 0+(707071433/2000000000 : ℝ)*X 0 1+(353364803/1000000000 : ℝ)*X 0 2+(640578343/1250000000 : ℝ)*X 1 0+(707071433/2000000000 : ℝ)*X 1 1+(353364803/1000000000 : ℝ)*X 1 2+(640578343/1250000000 : ℝ)*X 2 0+(707071433/2000000000 : ℝ)*X 2 1+(353364803/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325087_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((37053/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37053/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9175522712194276698157/1080850000000000000000000000 : ℝ) := by norm_num
    linear_combination (4824261/1000000000000 : ℝ)*(base19) + (11770947/1000000000000 : ℝ)*(base23) + (38921600563/100000000000 : ℝ)*(base50) + (72202957743/200000000000 : ℝ)*(base60) + (3534589184119/1000000000000 : ℝ)*(major_s1_0) + (3534589184119/1000000000000 : ℝ)*(major_s1_1) + (3534589184119/1000000000000 : ℝ)*(major_s1_2) + (6887463/500000000000 : ℝ)*(sp_s1_1) + (2655056927747/500000000000 : ℝ)*(sp_s1_7) + (2655060510449/500000000000 : ℝ)*(sp_s1_8) + (5310119442447/1000000000000 : ℝ)*(sp_s1_9) + (1759035918423/1000000000000 : ℝ)*(sp_s1_13) + (2576459/100000000000 : ℝ)*(sp_s1_14) + (840669/100000000000 : ℝ)*(sp_s1_23) + (1759035918423/1000000000000 : ℝ)*(f.failure) + (1327534905021/250000000000 : ℝ)*(f.sum) + (687166820405239/1080850000000000000000000000 : ℝ)*base62 + (39012336330671/101329687500000000000000000 : ℝ)*base64 + (1444557507277/12970200000000000000000000 : ℝ)*base67 + (557381162358967/648510000000000000000000000 : ℝ)*base68 + (143848212019239/1080850000000000000000000000 : ℝ)*base70 + (3103878963283357/3242550000000000000000000000 : ℝ)*base72 + (1568116732042151/1621275000000000000000000000 : ℝ)*base74 + (32890054330019/129702000000000000000000000 : ℝ)*base76 + (188490760952453/540425000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (99197/100000000000000000 : ℝ)*base87 + (99197/100000000000000000 : ℝ)*base89 + (99197/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((37053/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(37053/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (458776644791732784631/54042500000000000000000000 : ℝ) := by norm_num
    linear_combination (11770947/1000000000000 : ℝ)*(base13) + (4824257/1000000000000 : ℝ)*(base21) + (72202957743/200000000000 : ℝ)*(base40) + (38921600563/100000000000 : ℝ)*(base60) + (88364729603/25000000000 : ℝ)*(major_s1_0) + (88364729603/25000000000 : ℝ)*(major_s1_1) + (88364729603/25000000000 : ℝ)*(major_s1_2) + (2754983/200000000000 : ℝ)*(sp_s1_2) + (840669/100000000000 : ℝ)*(sp_s1_7) + (331882465153/62500000000 : ℝ)*(sp_s1_14) + (2655056927747/500000000000 : ℝ)*(sp_s1_15) + (2655060510457/500000000000 : ℝ)*(sp_s1_16) + (1759035918423/1000000000000 : ℝ)*(sp_s1_20) + (25764591/1000000000000 : ℝ)*(sp_s1_22) + (1759035918423/1000000000000 : ℝ)*(f.failure) + (1062027924017/200000000000 : ℝ)*(f.sum) + (88766107793111/216170000000000000000000000 : ℝ)*base63 + (118038590776409/324255000000000000000000000 : ℝ)*base64 + (11604825007309/162127500000000000000000000 : ℝ)*base67 + (283097447043181/648510000000000000000000000 : ℝ)*base69 + (62031780334459/108085000000000000000000000 : ℝ)*base70 + (35372639686937/162127500000000000000000000 : ℝ)*base73 + (42939123510451/64851000000000000000000000 : ℝ)*base74 + (169241484847/324255000000000000000000 : ℝ)*base76 + (5506570616829/27021250000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (803/100000000000000000 : ℝ)*base86 + (803/100000000000000000 : ℝ)*base88 + (803/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37053/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(37053/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1146939729842451156057/135106250000000000000000000 : ℝ) := by norm_num
    linear_combination (2412127/500000000000 : ℝ)*(base11) + (11770947/1000000000000 : ℝ)*(base15) + (38921600563/100000000000 : ℝ)*(base40) + (72202957743/200000000000 : ℝ)*(base50) + (3534589184121/1000000000000 : ℝ)*(major_s1_0) + (3534589184121/1000000000000 : ℝ)*(major_s1_1) + (3534589184121/1000000000000 : ℝ)*(major_s1_2) + (13774933/1000000000000 : ℝ)*(sp_s1_0) + (1610287/62500000000 : ℝ)*(sp_s1_9) + (840669/100000000000 : ℝ)*(sp_s1_15) + (5310121020899/1000000000000 : ℝ)*(sp_s1_21) + (106202388849/20000000000 : ℝ)*(sp_s1_22) + (2655056927747/500000000000 : ℝ)*(sp_s1_23) + (1759035918423/1000000000000 : ℝ)*(sp_s1_27) + (1759035918423/1000000000000 : ℝ)*(f.failure) + (2655069810043/500000000000 : ℝ)*(f.sum) + (294763430162597/540425000000000000000000000 : ℝ)*base63 + (59932067394571/270212500000000000000000000 : ℝ)*base65 + (3700127160721/13510625000000000000000000 : ℝ)*base67 + (66162204498769/216170000000000000000000000 : ℝ)*base68 + (259618068197927/540425000000000000000000000 : ℝ)*base71 + (99240470129273/540425000000000000000000000 : ℝ)*base72 + (110970847919123/135106250000000000000000000 : ℝ)*base75 + (10290979556719/13510625000000000000000000 : ℝ)*base77 + (553468786283941/1080850000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (100803/100000000000000000 : ℝ)*base86 + (100803/100000000000000000 : ℝ)*base88 + (100803/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p025_positive87 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  have ho : distinctOrders 87=![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] := by decide
  have hs : ![![true, true, true], ![true, true, true], ![true, true, true]]=(fun (_ _ : Fin 3) => true) := by decide
  have hh := collision_c325087 p hpa (by linarith only [hpb]) X (by simpa only [ho,hs] using hX)
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

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_positive87 p hpa hpb X hX

#print axioms solution
