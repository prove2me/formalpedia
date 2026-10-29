-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_positive63
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:33:30.655835+00:00
-- url     : https://prove2.me/submissions/76925cbc-0ac2-47e7-8d53-638c30b18c8c

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
theorem collision_support_c330063_s0_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-99238579/5000000000 : ℝ)*x 0 + (1085397447/2000000000 : ℝ)*x 1 + (2856034583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99238579/5000000000 : ℝ)^6 ≤ (453129819907/50000000000000 : ℝ)^5 := by
    have hnat : (99238579 : ℕ)^6*50000000000000^5 ≤ 453129819907^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99238579 5000000000 453129819907 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085397447/2000000000 : ℝ)^6 ≤ (48025352374209/100000000000000 : ℝ)^5 := by
    have hnat : (1085397447 : ℕ)^6*100000000000000^5 ≤ 48025352374209^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085397447 2000000000 48025352374209 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2856034583/5000000000 : ℝ)^6 ≤ (51068387968449/100000000000000 : ℝ)^5 := by
    have hnat : (2856034583 : ℕ)^6*100000000000000^5 ≤ 51068387968449^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2856034583 5000000000 51068387968449 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99238579/5000000000 : ℝ), (1085397447/2000000000 : ℝ), (2856034583/5000000000 : ℝ)] ![(453129819907/50000000000000 : ℝ), (48025352374209/100000000000000 : ℝ), (51068387968449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99238579/5000000000 : ℝ)|^6 ≤ (453129819907/50000000000000 : ℝ)^5
        have hw : |(-99238579/5000000000 : ℝ)|=(99238579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085397447/2000000000 : ℝ)|^6 ≤ (48025352374209/100000000000000 : ℝ)^5
        have hw : |(1085397447/2000000000 : ℝ)|=(1085397447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2856034583/5000000000 : ℝ)|^6 ≤ (51068387968449/100000000000000 : ℝ)^5
        have hw : |(2856034583/5000000000 : ℝ)|=(2856034583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_7 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-1573377311/10000000000 : ℝ)*x 0 + (1263628077/10000000000 : ℝ)*x 1 + (8370173619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1573377311/10000000000 : ℝ)^6 ≤ (5434623520789/50000000000000 : ℝ)^5 := by
    have hnat : (1573377311 : ℕ)^6*50000000000000^5 ≤ 5434623520789^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1573377311 10000000000 5434623520789 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1263628077/10000000000 : ℝ)^6 ≤ (8354935865631/100000000000000 : ℝ)^5 := by
    have hnat : (1263628077 : ℕ)^6*100000000000000^5 ≤ 8354935865631^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263628077 10000000000 8354935865631 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8370173619/10000000000 : ℝ)^6 ≤ (40387908539443/50000000000000 : ℝ)^5 := by
    have hnat : (8370173619 : ℕ)^6*50000000000000^5 ≤ 40387908539443^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8370173619 10000000000 40387908539443 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1573377311/10000000000 : ℝ), (1263628077/10000000000 : ℝ), (8370173619/10000000000 : ℝ)] ![(5434623520789/50000000000000 : ℝ), (8354935865631/100000000000000 : ℝ), (40387908539443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1573377311/10000000000 : ℝ)|^6 ≤ (5434623520789/50000000000000 : ℝ)^5
        have hw : |(-1573377311/10000000000 : ℝ)|=(1573377311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1263628077/10000000000 : ℝ)|^6 ≤ (8354935865631/100000000000000 : ℝ)^5
        have hw : |(1263628077/10000000000 : ℝ)|=(1263628077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8370173619/10000000000 : ℝ)|^6 ≤ (40387908539443/50000000000000 : ℝ)^5
        have hw : |(8370173619/10000000000 : ℝ)|=(8370173619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_8 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (501684719/2000000000 : ℝ)*x 0 + (-11320353/2000000000 : ℝ)*x 1 + (1046271711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501684719/2000000000 : ℝ)^6 ≤ (475577239133/2500000000000 : ℝ)^5 := by
    have hnat : (501684719 : ℕ)^6*2500000000000^5 ≤ 475577239133^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501684719 2000000000 475577239133 2500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11320353/2000000000 : ℝ)^6 ≤ (25136568019/12500000000000 : ℝ)^5 := by
    have hnat : (11320353 : ℕ)^6*12500000000000^5 ≤ 25136568019^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11320353 2000000000 25136568019 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046271711/1250000000 : ℝ)^6 ≤ (40387908938971/50000000000000 : ℝ)^5 := by
    have hnat : (1046271711 : ℕ)^6*50000000000000^5 ≤ 40387908938971^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046271711 1250000000 40387908938971 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(501684719/2000000000 : ℝ), (-11320353/2000000000 : ℝ), (1046271711/1250000000 : ℝ)] ![(475577239133/2500000000000 : ℝ), (25136568019/12500000000000 : ℝ), (40387908938971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(501684719/2000000000 : ℝ)|^6 ≤ (475577239133/2500000000000 : ℝ)^5
        have hw : |(501684719/2000000000 : ℝ)|=(501684719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11320353/2000000000 : ℝ)|^6 ≤ (25136568019/12500000000000 : ℝ)^5
        have hw : |(-11320353/2000000000 : ℝ)|=(11320353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046271711/1250000000 : ℝ)|^6 ≤ (40387908938971/50000000000000 : ℝ)^5
        have hw : |(1046271711/1250000000 : ℝ)|=(1046271711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_9 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1254211581/5000000000 : ℝ)*x 0 + (8370173629/10000000000 : ℝ)*x 1 + (-56602851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1254211581/5000000000 : ℝ)^6 ≤ (19023085624839/100000000000000 : ℝ)^5 := by
    have hnat : (1254211581 : ℕ)^6*100000000000000^5 ≤ 19023085624839^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254211581 5000000000 19023085624839 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8370173629/10000000000 : ℝ)^6 ≤ (80775817194691/100000000000000 : ℝ)^5 := by
    have hnat : (8370173629 : ℕ)^6*100000000000000^5 ≤ 80775817194691^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8370173629 10000000000 80775817194691 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56602851/10000000000 : ℝ)^6 ≤ (201097174119/100000000000000 : ℝ)^5 := by
    have hnat : (56602851 : ℕ)^6*100000000000000^5 ≤ 201097174119^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56602851 10000000000 201097174119 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1254211581/5000000000 : ℝ), (8370173629/10000000000 : ℝ), (-56602851/10000000000 : ℝ)] ![(19023085624839/100000000000000 : ℝ), (80775817194691/100000000000000 : ℝ), (201097174119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1254211581/5000000000 : ℝ)|^6 ≤ (19023085624839/100000000000000 : ℝ)^5
        have hw : |(1254211581/5000000000 : ℝ)|=(1254211581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8370173629/10000000000 : ℝ)|^6 ≤ (80775817194691/100000000000000 : ℝ)^5
        have hw : |(8370173629/10000000000 : ℝ)|=(8370173629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56602851/10000000000 : ℝ)|^6 ≤ (201097174119/100000000000000 : ℝ)^5
        have hw : |(-56602851/10000000000 : ℝ)|=(56602851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_13 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (3173672481/10000000000 : ℝ)*x 0 + (890158781/1250000000 : ℝ)*x 1 + (312110829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3173672481/10000000000 : ℝ)^6 ≤ (25227518150329/100000000000000 : ℝ)^5 := by
    have hnat : (3173672481 : ℕ)^6*100000000000000^5 ≤ 25227518150329^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3173672481 10000000000 25227518150329 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890158781/1250000000 : ℝ)^6 ≤ (16634470049951/25000000000000 : ℝ)^5 := by
    have hnat : (890158781 : ℕ)^6*25000000000000^5 ≤ 16634470049951^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890158781 1250000000 16634470049951 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312110829/2500000000 : ℝ)^6 ≤ (4117300818267/50000000000000 : ℝ)^5 := by
    have hnat : (312110829 : ℕ)^6*50000000000000^5 ≤ 4117300818267^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312110829 2500000000 4117300818267 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3173672481/10000000000 : ℝ), (890158781/1250000000 : ℝ), (312110829/2500000000 : ℝ)] ![(25227518150329/100000000000000 : ℝ), (16634470049951/25000000000000 : ℝ), (4117300818267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3173672481/10000000000 : ℝ)|^6 ≤ (25227518150329/100000000000000 : ℝ)^5
        have hw : |(3173672481/10000000000 : ℝ)|=(3173672481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(890158781/1250000000 : ℝ)|^6 ≤ (16634470049951/25000000000000 : ℝ)^5
        have hw : |(890158781/1250000000 : ℝ)|=(890158781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(312110829/2500000000 : ℝ)|^6 ≤ (4117300818267/50000000000000 : ℝ)^5
        have hw : |(312110829/2500000000 : ℝ)|=(312110829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_14 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-14842209/5000000000 : ℝ)*x 0 + (244997359/1000000000 : ℝ)*x 1 + (2106330679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14842209/5000000000 : ℝ)^6 ≤ (46345145557/50000000000000 : ℝ)^5 := by
    have hnat : (14842209 : ℕ)^6*50000000000000^5 ≤ 46345145557^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14842209 5000000000 46345145557 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244997359/1000000000 : ℝ)^6 ≤ (462310430603/2500000000000 : ℝ)^5 := by
    have hnat : (244997359 : ℕ)^6*2500000000000^5 ≤ 462310430603^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244997359 1000000000 462310430603 2500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106330679/2500000000 : ℝ)^6 ≤ (40707446236359/50000000000000 : ℝ)^5 := by
    have hnat : (2106330679 : ℕ)^6*50000000000000^5 ≤ 40707446236359^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106330679 2500000000 40707446236359 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14842209/5000000000 : ℝ), (244997359/1000000000 : ℝ), (2106330679/2500000000 : ℝ)] ![(46345145557/50000000000000 : ℝ), (462310430603/2500000000000 : ℝ), (40707446236359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14842209/5000000000 : ℝ)|^6 ≤ (46345145557/50000000000000 : ℝ)^5
        have hw : |(-14842209/5000000000 : ℝ)|=(14842209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(244997359/1000000000 : ℝ)|^6 ≤ (462310430603/2500000000000 : ℝ)^5
        have hw : |(244997359/1000000000 : ℝ)|=(244997359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2106330679/2500000000 : ℝ)|^6 ≤ (40707446236359/50000000000000 : ℝ)^5
        have hw : |(2106330679/2500000000 : ℝ)|=(2106330679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_15 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (231906097/2000000000 : ℝ)*x 0 + (-797524727/5000000000 : ℝ)*x 1 + (8425322221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (231906097/2000000000 : ℝ)^6 ≤ (7535960359/100000000000 : ℝ)^5 := by
    have hnat : (231906097 : ℕ)^6*100000000000^5 ≤ 7535960359^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231906097 2000000000 7535960359 100000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (797524727/5000000000 : ℝ)^6 ≤ (1381144112061/12500000000000 : ℝ)^5 := by
    have hnat : (797524727 : ℕ)^6*12500000000000^5 ≤ 1381144112061^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797524727 5000000000 1381144112061 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8425322221/10000000000 : ℝ)^6 ≤ (40707443366413/50000000000000 : ℝ)^5 := by
    have hnat : (8425322221 : ℕ)^6*50000000000000^5 ≤ 40707443366413^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8425322221 10000000000 40707443366413 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(231906097/2000000000 : ℝ), (-797524727/5000000000 : ℝ), (8425322221/10000000000 : ℝ)] ![(7535960359/100000000000 : ℝ), (1381144112061/12500000000000 : ℝ), (40707443366413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(231906097/2000000000 : ℝ)|^6 ≤ (7535960359/100000000000 : ℝ)^5
        have hw : |(231906097/2000000000 : ℝ)|=(231906097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-797524727/5000000000 : ℝ)|^6 ≤ (1381144112061/12500000000000 : ℝ)^5
        have hw : |(-797524727/5000000000 : ℝ)|=(797524727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8425322221/10000000000 : ℝ)|^6 ≤ (40707443366413/50000000000000 : ℝ)^5
        have hw : |(8425322221/10000000000 : ℝ)|=(8425322221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_16 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (8075397489/10000000000 : ℝ)*x 0 + (2860715809/10000000000 : ℝ)*x 1 + (-11312677/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8075397489/10000000000 : ℝ)^6 ≤ (19343573091381/25000000000000 : ℝ)^5 := by
    have hnat : (8075397489 : ℕ)^6*25000000000000^5 ≤ 19343573091381^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8075397489 10000000000 19343573091381 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2860715809/10000000000 : ℝ)^6 ≤ (22272535467707/100000000000000 : ℝ)^5 := by
    have hnat : (2860715809 : ℕ)^6*100000000000000^5 ≤ 22272535467707^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2860715809 10000000000 22272535467707 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11312677/1250000000 : ℝ)^6 ≤ (176586074979/50000000000000 : ℝ)^5 := by
    have hnat : (11312677 : ℕ)^6*50000000000000^5 ≤ 176586074979^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11312677 1250000000 176586074979 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8075397489/10000000000 : ℝ), (2860715809/10000000000 : ℝ), (-11312677/1250000000 : ℝ)] ![(19343573091381/25000000000000 : ℝ), (22272535467707/100000000000000 : ℝ), (176586074979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8075397489/10000000000 : ℝ)|^6 ≤ (19343573091381/25000000000000 : ℝ)^5
        have hw : |(8075397489/10000000000 : ℝ)|=(8075397489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2860715809/10000000000 : ℝ)|^6 ≤ (22272535467707/100000000000000 : ℝ)^5
        have hw : |(2860715809/10000000000 : ℝ)|=(2860715809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11312677/1250000000 : ℝ)|^6 ≤ (176586074979/50000000000000 : ℝ)^5
        have hw : |(-11312677/1250000000 : ℝ)|=(11312677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_20 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (7432172511/10000000000 : ℝ)*x 0 + (1398187763/5000000000 : ℝ)*x 1 + (1255234381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7432172511/10000000000 : ℝ)^6 ≤ (35019419470353/50000000000000 : ℝ)^5 := by
    have hnat : (7432172511 : ℕ)^6*50000000000000^5 ≤ 35019419470353^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7432172511 10000000000 35019419470353 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1398187763/5000000000 : ℝ)^6 ≤ (2709097303591/12500000000000 : ℝ)^5 := by
    have hnat : (1398187763 : ℕ)^6*12500000000000^5 ≤ 2709097303591^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398187763 5000000000 2709097303591 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255234381/10000000000 : ℝ)^6 ≤ (8288382619187/100000000000000 : ℝ)^5 := by
    have hnat : (1255234381 : ℕ)^6*100000000000000^5 ≤ 8288382619187^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255234381 10000000000 8288382619187 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7432172511/10000000000 : ℝ), (1398187763/5000000000 : ℝ), (1255234381/10000000000 : ℝ)] ![(35019419470353/50000000000000 : ℝ), (2709097303591/12500000000000 : ℝ), (8288382619187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7432172511/10000000000 : ℝ)|^6 ≤ (35019419470353/50000000000000 : ℝ)^5
        have hw : |(7432172511/10000000000 : ℝ)|=(7432172511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1398187763/5000000000 : ℝ)|^6 ≤ (2709097303591/12500000000000 : ℝ)^5
        have hw : |(1398187763/5000000000 : ℝ)|=(1398187763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1255234381/10000000000 : ℝ)|^6 ≤ (8288382619187/100000000000000 : ℝ)^5
        have hw : |(1255234381/10000000000 : ℝ)|=(1255234381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_21 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-126204349/10000000000 : ℝ)*x 0 + (3558500973/5000000000 : ℝ)*x 1 + (3968092471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126204349/10000000000 : ℝ)^6 ≤ (52636764393/10000000000000 : ℝ)^5 := by
    have hnat : (126204349 : ℕ)^6*10000000000000^5 ≤ 52636764393^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126204349 10000000000 52636764393 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3558500973/5000000000 : ℝ)^6 ≤ (8311253225407/12500000000000 : ℝ)^5 := by
    have hnat : (3558500973 : ℕ)^6*12500000000000^5 ≤ 8311253225407^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3558500973 5000000000 8311253225407 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3968092471/10000000000 : ℝ)^6 ≤ (32983606535951/100000000000000 : ℝ)^5 := by
    have hnat : (3968092471 : ℕ)^6*100000000000000^5 ≤ 32983606535951^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3968092471 10000000000 32983606535951 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126204349/10000000000 : ℝ), (3558500973/5000000000 : ℝ), (3968092471/10000000000 : ℝ)] ![(52636764393/10000000000000 : ℝ), (8311253225407/12500000000000 : ℝ), (32983606535951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126204349/10000000000 : ℝ)|^6 ≤ (52636764393/10000000000000 : ℝ)^5
        have hw : |(-126204349/10000000000 : ℝ)|=(126204349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3558500973/5000000000 : ℝ)|^6 ≤ (8311253225407/12500000000000 : ℝ)^5
        have hw : |(3558500973/5000000000 : ℝ)|=(3558500973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3968092471/10000000000 : ℝ)|^6 ≤ (32983606535951/100000000000000 : ℝ)^5
        have hw : |(3968092471/10000000000 : ℝ)|=(3968092471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_22 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4019018219/5000000000 : ℝ)*x 0 + (-17975199/10000000000 : ℝ)*x 1 + (2938828927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4019018219/5000000000 : ℝ)^6 ≤ (38472461087401/50000000000000 : ℝ)^5 := by
    have hnat : (4019018219 : ℕ)^6*50000000000000^5 ≤ 38472461087401^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019018219 5000000000 38472461087401 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17975199/10000000000 : ℝ)^6 ≤ (5077015023/10000000000000 : ℝ)^5 := by
    have hnat : (17975199 : ℕ)^6*10000000000000^5 ≤ 5077015023^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17975199 10000000000 5077015023 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2938828927/10000000000 : ℝ)^6 ≤ (11502153828343/50000000000000 : ℝ)^5 := by
    have hnat : (2938828927 : ℕ)^6*50000000000000^5 ≤ 11502153828343^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2938828927 10000000000 11502153828343 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4019018219/5000000000 : ℝ), (-17975199/10000000000 : ℝ), (2938828927/10000000000 : ℝ)] ![(38472461087401/50000000000000 : ℝ), (5077015023/10000000000000 : ℝ), (11502153828343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4019018219/5000000000 : ℝ)|^6 ≤ (38472461087401/50000000000000 : ℝ)^5
        have hw : |(4019018219/5000000000 : ℝ)|=(4019018219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17975199/10000000000 : ℝ)|^6 ≤ (5077015023/10000000000000 : ℝ)^5
        have hw : |(-17975199/10000000000 : ℝ)|=(17975199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2938828927/10000000000 : ℝ)|^6 ≤ (11502153828343/50000000000000 : ℝ)^5
        have hw : |(2938828927/10000000000 : ℝ)|=(2938828927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_23 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (464607099/5000000000 : ℝ)*x 0 + (8560005467/10000000000 : ℝ)*x 1 + (-404595453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464607099/5000000000 : ℝ)^6 ≤ (5777487365537/100000000000000 : ℝ)^5 := by
    have hnat : (464607099 : ℕ)^6*100000000000000^5 ≤ 5777487365537^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464607099 5000000000 5777487365537 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8560005467/10000000000 : ℝ)^6 ≤ (20744781225971/25000000000000 : ℝ)^5 := by
    have hnat : (8560005467 : ℕ)^6*25000000000000^5 ≤ 20744781225971^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8560005467 10000000000 20744781225971 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404595453/2500000000 : ℝ)^6 ≤ (1124338770901/10000000000000 : ℝ)^5 := by
    have hnat : (404595453 : ℕ)^6*10000000000000^5 ≤ 1124338770901^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404595453 2500000000 1124338770901 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(464607099/5000000000 : ℝ), (8560005467/10000000000 : ℝ), (-404595453/2500000000 : ℝ)] ![(5777487365537/100000000000000 : ℝ), (20744781225971/25000000000000 : ℝ), (1124338770901/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(464607099/5000000000 : ℝ)|^6 ≤ (5777487365537/100000000000000 : ℝ)^5
        have hw : |(464607099/5000000000 : ℝ)|=(464607099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8560005467/10000000000 : ℝ)|^6 ≤ (20744781225971/25000000000000 : ℝ)^5
        have hw : |(8560005467/10000000000 : ℝ)|=(8560005467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-404595453/2500000000 : ℝ)|^6 ≤ (1124338770901/10000000000000 : ℝ)^5
        have hw : |(-404595453/2500000000 : ℝ)|=(404595453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s0_27 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (7540067751/10000000000 : ℝ)*x 0 + (116196919/500000000 : ℝ)*x 1 + (327009543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7540067751/10000000000 : ℝ)^6 ≤ (71260735068183/100000000000000 : ℝ)^5 := by
    have hnat : (7540067751 : ℕ)^6*100000000000000^5 ≤ 71260735068183^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7540067751 10000000000 71260735068183 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116196919/500000000 : ℝ)^6 ≤ (17356794840889/100000000000000 : ℝ)^5 := by
    have hnat : (116196919 : ℕ)^6*100000000000000^5 ≤ 17356794840889^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116196919 500000000 17356794840889 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327009543/2000000000 : ℝ)^6 ≤ (1138247007613/10000000000000 : ℝ)^5 := by
    have hnat : (327009543 : ℕ)^6*10000000000000^5 ≤ 1138247007613^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327009543 2000000000 1138247007613 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7540067751/10000000000 : ℝ), (116196919/500000000 : ℝ), (327009543/2000000000 : ℝ)] ![(71260735068183/100000000000000 : ℝ), (17356794840889/100000000000000 : ℝ), (1138247007613/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7540067751/10000000000 : ℝ)|^6 ≤ (71260735068183/100000000000000 : ℝ)^5
        have hw : |(7540067751/10000000000 : ℝ)|=(7540067751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(116196919/500000000 : ℝ)|^6 ≤ (17356794840889/100000000000000 : ℝ)^5
        have hw : |(116196919/500000000 : ℝ)|=(116196919/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327009543/2000000000 : ℝ)|^6 ≤ (1138247007613/10000000000000 : ℝ)^5
        have hw : |(327009543/2000000000 : ℝ)|=(327009543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-983386633/10000000000 : ℝ)*x 0 + (2656592363/5000000000 : ℝ)*x 1 + (5329936349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983386633/10000000000 : ℝ)^6 ≤ (1545998860643/25000000000000 : ℝ)^5 := by
    have hnat : (983386633 : ℕ)^6*25000000000000^5 ≤ 1545998860643^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983386633 10000000000 1545998860643 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2656592363/5000000000 : ℝ)^6 ≤ (9363881180831/20000000000000 : ℝ)^5 := by
    have hnat : (2656592363 : ℕ)^6*20000000000000^5 ≤ 9363881180831^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656592363 5000000000 9363881180831 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5329936349/10000000000 : ℝ)^6 ≤ (46996598638209/100000000000000 : ℝ)^5 := by
    have hnat : (5329936349 : ℕ)^6*100000000000000^5 ≤ 46996598638209^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5329936349 10000000000 46996598638209 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-983386633/10000000000 : ℝ), (2656592363/5000000000 : ℝ), (5329936349/10000000000 : ℝ)] ![(1545998860643/25000000000000 : ℝ), (9363881180831/20000000000000 : ℝ), (46996598638209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-983386633/10000000000 : ℝ)|^6 ≤ (1545998860643/25000000000000 : ℝ)^5
        have hw : |(-983386633/10000000000 : ℝ)|=(983386633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2656592363/5000000000 : ℝ)|^6 ≤ (9363881180831/20000000000000 : ℝ)^5
        have hw : |(2656592363/5000000000 : ℝ)|=(2656592363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5329936349/10000000000 : ℝ)|^6 ≤ (46996598638209/100000000000000 : ℝ)^5
        have hw : |(5329936349/10000000000 : ℝ)|=(5329936349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5313124191/10000000000 : ℝ)*x 0 + (-245710491/2500000000 : ℝ)*x 1 + (5330385269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5313124191/10000000000 : ℝ)^6 ≤ (46818765788747/100000000000000 : ℝ)^5 := by
    have hnat : (5313124191 : ℕ)^6*100000000000000^5 ≤ 46818765788747^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5313124191 10000000000 46818765788747 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245710491/2500000000 : ℝ)^6 ≤ (6179885509917/100000000000000 : ℝ)^5 := by
    have hnat : (245710491 : ℕ)^6*100000000000000^5 ≤ 6179885509917^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245710491 2500000000 6179885509917 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5330385269/10000000000 : ℝ)^6 ≤ (47001348689101/100000000000000 : ℝ)^5 := by
    have hnat : (5330385269 : ℕ)^6*100000000000000^5 ≤ 47001348689101^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5330385269 10000000000 47001348689101 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5313124191/10000000000 : ℝ), (-245710491/2500000000 : ℝ), (5330385269/10000000000 : ℝ)] ![(46818765788747/100000000000000 : ℝ), (6179885509917/100000000000000 : ℝ), (47001348689101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5313124191/10000000000 : ℝ)|^6 ≤ (46818765788747/100000000000000 : ℝ)^5
        have hw : |(5313124191/10000000000 : ℝ)|=(5313124191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245710491/2500000000 : ℝ)|^6 ≤ (6179885509917/100000000000000 : ℝ)^5
        have hw : |(-245710491/2500000000 : ℝ)|=(245710491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5330385269/10000000000 : ℝ)|^6 ≤ (47001348689101/100000000000000 : ℝ)^5
        have hw : |(5330385269/10000000000 : ℝ)|=(5330385269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5325682299/10000000000 : ℝ)*x 0 + (5327936411/10000000000 : ℝ)*x 1 + (-484325921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5325682299/10000000000 : ℝ)^6 ≤ (46951590238781/100000000000000 : ℝ)^5 := by
    have hnat : (5325682299 : ℕ)^6*100000000000000^5 ≤ 46951590238781^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5325682299 10000000000 46951590238781 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5327936411/10000000000 : ℝ)^6 ≤ (1879017525607/4000000000000 : ℝ)^5 := by
    have hnat : (5327936411 : ℕ)^6*4000000000000^5 ≤ 1879017525607^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5327936411 10000000000 1879017525607 4000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (484325921/5000000000 : ℝ)^6 ≤ (6072971603189/100000000000000 : ℝ)^5 := by
    have hnat : (484325921 : ℕ)^6*100000000000000^5 ≤ 6072971603189^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484325921 5000000000 6072971603189 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5325682299/10000000000 : ℝ), (5327936411/10000000000 : ℝ), (-484325921/5000000000 : ℝ)] ![(46951590238781/100000000000000 : ℝ), (1879017525607/4000000000000 : ℝ), (6072971603189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5325682299/10000000000 : ℝ)|^6 ≤ (46951590238781/100000000000000 : ℝ)^5
        have hw : |(5325682299/10000000000 : ℝ)|=(5325682299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5327936411/10000000000 : ℝ)|^6 ≤ (1879017525607/4000000000000 : ℝ)^5
        have hw : |(5327936411/10000000000 : ℝ)|=(5327936411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-484325921/5000000000 : ℝ)|^6 ≤ (6072971603189/100000000000000 : ℝ)^5
        have hw : |(-484325921/5000000000 : ℝ)|=(484325921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_6 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (802661583/2000000000 : ℝ)*x 0 + (250436217/625000000 : ℝ)*x 1 + (3989074267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (802661583/2000000000 : ℝ)^6 ≤ (33435127058397/100000000000000 : ℝ)^5 := by
    have hnat : (802661583 : ℕ)^6*100000000000000^5 ≤ 33435127058397^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802661583 2000000000 33435127058397 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250436217/625000000 : ℝ)^6 ≤ (3337186983887/10000000000000 : ℝ)^5 := by
    have hnat : (250436217 : ℕ)^6*10000000000000^5 ≤ 3337186983887^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250436217 625000000 3337186983887 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3989074267/10000000000 : ℝ)^6 ≤ (33193003084163/100000000000000 : ℝ)^5 := by
    have hnat : (3989074267 : ℕ)^6*100000000000000^5 ≤ 33193003084163^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3989074267 10000000000 33193003084163 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(802661583/2000000000 : ℝ), (250436217/625000000 : ℝ), (3989074267/10000000000 : ℝ)] ![(33435127058397/100000000000000 : ℝ), (3337186983887/10000000000000 : ℝ), (33193003084163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(802661583/2000000000 : ℝ)|^6 ≤ (33435127058397/100000000000000 : ℝ)^5
        have hw : |(802661583/2000000000 : ℝ)|=(802661583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250436217/625000000 : ℝ)|^6 ≤ (3337186983887/10000000000000 : ℝ)^5
        have hw : |(250436217/625000000 : ℝ)|=(250436217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3989074267/10000000000 : ℝ)|^6 ≤ (33193003084163/100000000000000 : ℝ)^5
        have hw : |(3989074267/10000000000 : ℝ)|=(3989074267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_7 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-91814401/1000000000 : ℝ)*x 0 + (4754569291/10000000000 : ℝ)*x 1 + (5921982669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91814401/1000000000 : ℝ)^6 ≤ (5694990005649/100000000000000 : ℝ)^5 := by
    have hnat : (91814401 : ℕ)^6*100000000000000^5 ≤ 5694990005649^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91814401 1000000000 5694990005649 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4754569291/10000000000 : ℝ)^6 ≤ (2048818191241/5000000000000 : ℝ)^5 := by
    have hnat : (4754569291 : ℕ)^6*5000000000000^5 ≤ 2048818191241^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4754569291 10000000000 2048818191241 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5921982669/10000000000 : ℝ)^6 ≤ (53328646157207/100000000000000 : ℝ)^5 := by
    have hnat : (5921982669 : ℕ)^6*100000000000000^5 ≤ 53328646157207^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5921982669 10000000000 53328646157207 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91814401/1000000000 : ℝ), (4754569291/10000000000 : ℝ), (5921982669/10000000000 : ℝ)] ![(5694990005649/100000000000000 : ℝ), (2048818191241/5000000000000 : ℝ), (53328646157207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91814401/1000000000 : ℝ)|^6 ≤ (5694990005649/100000000000000 : ℝ)^5
        have hw : |(-91814401/1000000000 : ℝ)|=(91814401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4754569291/10000000000 : ℝ)|^6 ≤ (2048818191241/5000000000000 : ℝ)^5
        have hw : |(4754569291/10000000000 : ℝ)|=(4754569291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5921982669/10000000000 : ℝ)|^6 ≤ (53328646157207/100000000000000 : ℝ)^5
        have hw : |(5921982669/10000000000 : ℝ)|=(5921982669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_8 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1270243901/2500000000 : ℝ)*x 0 + (-429991881/10000000000 : ℝ)*x 1 + (2961216669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1270243901/2500000000 : ℝ)^6 ≤ (11093703140313/25000000000000 : ℝ)^5 := by
    have hnat : (1270243901 : ℕ)^6*25000000000000^5 ≤ 11093703140313^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270243901 2500000000 11093703140313 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429991881/10000000000 : ℝ)^6 ≤ (2291671197913/100000000000000 : ℝ)^5 := by
    have hnat : (429991881 : ℕ)^6*100000000000000^5 ≤ 2291671197913^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429991881 10000000000 2291671197913 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2961216669/5000000000 : ℝ)^6 ≤ (53333516232357/100000000000000 : ℝ)^5 := by
    have hnat : (2961216669 : ℕ)^6*100000000000000^5 ≤ 53333516232357^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961216669 5000000000 53333516232357 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1270243901/2500000000 : ℝ), (-429991881/10000000000 : ℝ), (2961216669/5000000000 : ℝ)] ![(11093703140313/25000000000000 : ℝ), (2291671197913/100000000000000 : ℝ), (53333516232357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1270243901/2500000000 : ℝ)|^6 ≤ (11093703140313/25000000000000 : ℝ)^5
        have hw : |(1270243901/2500000000 : ℝ)|=(1270243901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429991881/10000000000 : ℝ)|^6 ≤ (2291671197913/100000000000000 : ℝ)^5
        have hw : |(-429991881/10000000000 : ℝ)|=(429991881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2961216669/5000000000 : ℝ)|^6 ≤ (53333516232357/100000000000000 : ℝ)^5
        have hw : |(2961216669/5000000000 : ℝ)|=(2961216669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_9 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (611033481/1250000000 : ℝ)*x 0 + (1529918961/2500000000 : ℝ)*x 1 + (-400486/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (611033481/1250000000 : ℝ)^6 ≤ (4236293033607/10000000000000 : ℝ)^5 := by
    have hnat : (611033481 : ℕ)^6*10000000000000^5 ≤ 4236293033607^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611033481 1250000000 4236293033607 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1529918961/2500000000 : ℝ)^6 ≤ (55472035479809/100000000000000 : ℝ)^5 := by
    have hnat : (1529918961 : ℕ)^6*100000000000000^5 ≤ 55472035479809^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529918961 2500000000 55472035479809 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400486/9765625 : ℝ)^6 ≤ (433006833493/20000000000000 : ℝ)^5 := by
    have hnat : (400486 : ℕ)^6*20000000000000^5 ≤ 433006833493^5*9765625^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400486 9765625 433006833493 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(611033481/1250000000 : ℝ), (1529918961/2500000000 : ℝ), (-400486/9765625 : ℝ)] ![(4236293033607/10000000000000 : ℝ), (55472035479809/100000000000000 : ℝ), (433006833493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(611033481/1250000000 : ℝ)|^6 ≤ (4236293033607/10000000000000 : ℝ)^5
        have hw : |(611033481/1250000000 : ℝ)|=(611033481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1529918961/2500000000 : ℝ)|^6 ≤ (55472035479809/100000000000000 : ℝ)^5
        have hw : |(1529918961/2500000000 : ℝ)|=(1529918961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-400486/9765625 : ℝ)|^6 ≤ (433006833493/20000000000000 : ℝ)^5
        have hw : |(-400486/9765625 : ℝ)|=(400486/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_13 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (449274499/1000000000 : ℝ)*x 0 + (214534189/400000000 : ℝ)*x 1 + (1985072643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449274499/1000000000 : ℝ)^6 ≤ (38283719211661/100000000000000 : ℝ)^5 := by
    have hnat : (449274499 : ℕ)^6*100000000000000^5 ≤ 38283719211661^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449274499 1000000000 38283719211661 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214534189/400000000 : ℝ)^6 ≤ (5918802367909/12500000000000 : ℝ)^5 := by
    have hnat : (214534189 : ℕ)^6*12500000000000^5 ≤ 5918802367909^5*400000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214534189 400000000 5918802367909 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1985072643/10000000000 : ℝ)^6 ≤ (359146545737/2500000000000 : ℝ)^5 := by
    have hnat : (1985072643 : ℕ)^6*2500000000000^5 ≤ 359146545737^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985072643 10000000000 359146545737 2500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(449274499/1000000000 : ℝ), (214534189/400000000 : ℝ), (1985072643/10000000000 : ℝ)] ![(38283719211661/100000000000000 : ℝ), (5918802367909/12500000000000 : ℝ), (359146545737/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(449274499/1000000000 : ℝ)|^6 ≤ (38283719211661/100000000000000 : ℝ)^5
        have hw : |(449274499/1000000000 : ℝ)|=(449274499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(214534189/400000000 : ℝ)|^6 ≤ (5918802367909/12500000000000 : ℝ)^5
        have hw : |(214534189/400000000 : ℝ)|=(214534189/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1985072643/10000000000 : ℝ)|^6 ≤ (359146545737/2500000000000 : ℝ)^5
        have hw : |(1985072643/10000000000 : ℝ)|=(1985072643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_14 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-217931971/5000000000 : ℝ)*x 0 + (5088264683/10000000000 : ℝ)*x 1 + (2955940713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217931971/5000000000 : ℝ)^6 ≤ (582319239891/25000000000000 : ℝ)^5 := by
    have hnat : (217931971 : ℕ)^6*25000000000000^5 ≤ 582319239891^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217931971 5000000000 582319239891 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5088264683/10000000000 : ℝ)^6 ≤ (44451214714767/100000000000000 : ℝ)^5 := by
    have hnat : (5088264683 : ℕ)^6*100000000000000^5 ≤ 44451214714767^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088264683 10000000000 44451214714767 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2955940713/5000000000 : ℝ)^6 ≤ (53219508312543/100000000000000 : ℝ)^5 := by
    have hnat : (2955940713 : ℕ)^6*100000000000000^5 ≤ 53219508312543^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2955940713 5000000000 53219508312543 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217931971/5000000000 : ℝ), (5088264683/10000000000 : ℝ), (2955940713/5000000000 : ℝ)] ![(582319239891/25000000000000 : ℝ), (44451214714767/100000000000000 : ℝ), (53219508312543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217931971/5000000000 : ℝ)|^6 ≤ (582319239891/25000000000000 : ℝ)^5
        have hw : |(-217931971/5000000000 : ℝ)|=(217931971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5088264683/10000000000 : ℝ)|^6 ≤ (44451214714767/100000000000000 : ℝ)^5
        have hw : |(5088264683/10000000000 : ℝ)|=(5088264683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2955940713/5000000000 : ℝ)|^6 ≤ (53219508312543/100000000000000 : ℝ)^5
        have hw : |(2955940713/5000000000 : ℝ)|=(2955940713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_15 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2384865497/5000000000 : ℝ)*x 0 + (-455535459/5000000000 : ℝ)*x 1 + (1182466859/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2384865497/5000000000 : ℝ)^6 ≤ (20566607868679/50000000000000 : ℝ)^5 := by
    have hnat : (2384865497 : ℕ)^6*50000000000000^5 ≤ 20566607868679^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384865497 5000000000 20566607868679 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455535459/5000000000 : ℝ)^6 ≤ (88162246213/1562500000000 : ℝ)^5 := by
    have hnat : (455535459 : ℕ)^6*1562500000000^5 ≤ 88162246213^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455535459 5000000000 88162246213 1562500000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1182466859/2000000000 : ℝ)^6 ≤ (53224400491203/100000000000000 : ℝ)^5 := by
    have hnat : (1182466859 : ℕ)^6*100000000000000^5 ≤ 53224400491203^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182466859 2000000000 53224400491203 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2384865497/5000000000 : ℝ), (-455535459/5000000000 : ℝ), (1182466859/2000000000 : ℝ)] ![(20566607868679/50000000000000 : ℝ), (88162246213/1562500000000 : ℝ), (53224400491203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2384865497/5000000000 : ℝ)|^6 ≤ (20566607868679/50000000000000 : ℝ)^5
        have hw : |(2384865497/5000000000 : ℝ)|=(2384865497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-455535459/5000000000 : ℝ)|^6 ≤ (88162246213/1562500000000 : ℝ)^5
        have hw : |(-455535459/5000000000 : ℝ)|=(455535459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1182466859/2000000000 : ℝ)|^6 ≤ (53224400491203/100000000000000 : ℝ)^5
        have hw : |(1182466859/2000000000 : ℝ)|=(1182466859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_16 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2953376941/5000000000 : ℝ)*x 0 + (1275773123/2500000000 : ℝ)*x 1 + (-420197363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2953376941/5000000000 : ℝ)^6 ≤ (53164122554149/100000000000000 : ℝ)^5 := by
    have hnat : (2953376941 : ℕ)^6*100000000000000^5 ≤ 53164122554149^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2953376941 5000000000 53164122554149 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1275773123/2500000000 : ℝ)^6 ≤ (44606703335109/100000000000000 : ℝ)^5 := by
    have hnat : (1275773123 : ℕ)^6*100000000000000^5 ≤ 44606703335109^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275773123 2500000000 44606703335109 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420197363/10000000000 : ℝ)^6 ≤ (1114587046499/50000000000000 : ℝ)^5 := by
    have hnat : (420197363 : ℕ)^6*50000000000000^5 ≤ 1114587046499^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420197363 10000000000 1114587046499 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2953376941/5000000000 : ℝ), (1275773123/2500000000 : ℝ), (-420197363/10000000000 : ℝ)] ![(53164122554149/100000000000000 : ℝ), (44606703335109/100000000000000 : ℝ), (1114587046499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2953376941/5000000000 : ℝ)|^6 ≤ (53164122554149/100000000000000 : ℝ)^5
        have hw : |(2953376941/5000000000 : ℝ)|=(2953376941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1275773123/2500000000 : ℝ)|^6 ≤ (44606703335109/100000000000000 : ℝ)^5
        have hw : |(1275773123/2500000000 : ℝ)|=(1275773123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420197363/10000000000 : ℝ)|^6 ≤ (1114587046499/50000000000000 : ℝ)^5
        have hw : |(-420197363/10000000000 : ℝ)|=(420197363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_20 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (377845931/625000000 : ℝ)*x 0 + (3733248881/10000000000 : ℝ)*x 1 + (1010488919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (377845931/625000000 : ℝ)^6 ≤ (27333275776241/50000000000000 : ℝ)^5 := by
    have hnat : (377845931 : ℕ)^6*50000000000000^5 ≤ 27333275776241^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377845931 625000000 27333275776241 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3733248881/10000000000 : ℝ)^6 ≤ (7663803148599/25000000000000 : ℝ)^5 := by
    have hnat : (3733248881 : ℕ)^6*25000000000000^5 ≤ 7663803148599^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733248881 10000000000 7663803148599 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010488919/5000000000 : ℝ)^6 ≤ (1467823583737/10000000000000 : ℝ)^5 := by
    have hnat : (1010488919 : ℕ)^6*10000000000000^5 ≤ 1467823583737^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010488919 5000000000 1467823583737 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(377845931/625000000 : ℝ), (3733248881/10000000000 : ℝ), (1010488919/5000000000 : ℝ)] ![(27333275776241/50000000000000 : ℝ), (7663803148599/25000000000000 : ℝ), (1467823583737/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(377845931/625000000 : ℝ)|^6 ≤ (27333275776241/50000000000000 : ℝ)^5
        have hw : |(377845931/625000000 : ℝ)|=(377845931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3733248881/10000000000 : ℝ)|^6 ≤ (7663803148599/25000000000000 : ℝ)^5
        have hw : |(3733248881/10000000000 : ℝ)|=(3733248881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010488919/5000000000 : ℝ)|^6 ≤ (1467823583737/10000000000000 : ℝ)^5
        have hw : |(1010488919/5000000000 : ℝ)|=(1010488919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_21 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-387722239/10000000000 : ℝ)*x 0 + (5668486261/10000000000 : ℝ)*x 1 + (107313059/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387722239/10000000000 : ℝ)^6 ≤ (506016715209/25000000000000 : ℝ)^5 := by
    have hnat : (387722239 : ℕ)^6*25000000000000^5 ≤ 506016715209^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387722239 10000000000 506016715209 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5668486261/10000000000 : ℝ)^6 ≤ (12650291314823/25000000000000 : ℝ)^5 := by
    have hnat : (5668486261 : ℕ)^6*25000000000000^5 ≤ 12650291314823^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5668486261 10000000000 12650291314823 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107313059/200000000 : ℝ)^6 ≤ (47374767863237/100000000000000 : ℝ)^5 := by
    have hnat : (107313059 : ℕ)^6*100000000000000^5 ≤ 47374767863237^5*200000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107313059 200000000 47374767863237 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-387722239/10000000000 : ℝ), (5668486261/10000000000 : ℝ), (107313059/200000000 : ℝ)] ![(506016715209/25000000000000 : ℝ), (12650291314823/25000000000000 : ℝ), (47374767863237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-387722239/10000000000 : ℝ)|^6 ≤ (506016715209/25000000000000 : ℝ)^5
        have hw : |(-387722239/10000000000 : ℝ)|=(387722239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5668486261/10000000000 : ℝ)|^6 ≤ (12650291314823/25000000000000 : ℝ)^5
        have hw : |(5668486261/10000000000 : ℝ)|=(5668486261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107313059/200000000 : ℝ)|^6 ≤ (47374767863237/100000000000000 : ℝ)^5
        have hw : |(107313059/200000000 : ℝ)|=(107313059/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_22 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1188455027/2000000000 : ℝ)*x 0 + (-47935947/1250000000 : ℝ)*x 1 + (5088570963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1188455027/2000000000 : ℝ)^6 ≤ (2677400325983/5000000000000 : ℝ)^5 := by
    have hnat : (1188455027 : ℕ)^6*5000000000000^5 ≤ 2677400325983^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188455027 2000000000 2677400325983 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47935947/1250000000 : ℝ)^6 ≤ (1950749937/97656250000 : ℝ)^5 := by
    have hnat : (47935947 : ℕ)^6*97656250000^5 ≤ 1950749937^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47935947 1250000000 1950749937 97656250000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5088570963/10000000000 : ℝ)^6 ≤ (44454425538301/100000000000000 : ℝ)^5 := by
    have hnat : (5088570963 : ℕ)^6*100000000000000^5 ≤ 44454425538301^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088570963 10000000000 44454425538301 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1188455027/2000000000 : ℝ), (-47935947/1250000000 : ℝ), (5088570963/10000000000 : ℝ)] ![(2677400325983/5000000000000 : ℝ), (1950749937/97656250000 : ℝ), (44454425538301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1188455027/2000000000 : ℝ)|^6 ≤ (2677400325983/5000000000000 : ℝ)^5
        have hw : |(1188455027/2000000000 : ℝ)|=(1188455027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47935947/1250000000 : ℝ)|^6 ≤ (1950749937/97656250000 : ℝ)^5
        have hw : |(-47935947/1250000000 : ℝ)|=(47935947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5088570963/10000000000 : ℝ)|^6 ≤ (44454425538301/100000000000000 : ℝ)^5
        have hw : |(5088570963/10000000000 : ℝ)|=(5088570963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_23 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1181974511/2500000000 : ℝ)*x 0 + (5960845769/10000000000 : ℝ)*x 1 + (-35947233/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1181974511/2500000000 : ℝ)^6 ≤ (40700685419611/100000000000000 : ℝ)^5 := by
    have hnat : (1181974511 : ℕ)^6*100000000000000^5 ≤ 40700685419611^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181974511 2500000000 40700685419611 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5960845769/10000000000 : ℝ)^6 ≤ (26874442662867/50000000000000 : ℝ)^5 := by
    have hnat : (5960845769 : ℕ)^6*50000000000000^5 ≤ 26874442662867^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5960845769 10000000000 26874442662867 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35947233/400000000 : ℝ)^6 ≤ (1110085847981/20000000000000 : ℝ)^5 := by
    have hnat : (35947233 : ℕ)^6*20000000000000^5 ≤ 1110085847981^5*400000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35947233 400000000 1110085847981 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1181974511/2500000000 : ℝ), (5960845769/10000000000 : ℝ), (-35947233/400000000 : ℝ)] ![(40700685419611/100000000000000 : ℝ), (26874442662867/50000000000000 : ℝ), (1110085847981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1181974511/2500000000 : ℝ)|^6 ≤ (40700685419611/100000000000000 : ℝ)^5
        have hw : |(1181974511/2500000000 : ℝ)|=(1181974511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5960845769/10000000000 : ℝ)|^6 ≤ (26874442662867/50000000000000 : ℝ)^5
        have hw : |(5960845769/10000000000 : ℝ)|=(5960845769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35947233/400000000 : ℝ)|^6 ≤ (1110085847981/20000000000000 : ℝ)^5
        have hw : |(-35947233/400000000 : ℝ)|=(35947233/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330063_s1_27 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (3119572707/5000000000 : ℝ)*x 0 + (2844291057/10000000000 : ℝ)*x 1 + (68384511/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3119572707/5000000000 : ℝ)^6 ≤ (3548380195131/6250000000000 : ℝ)^5 := by
    have hnat : (3119572707 : ℕ)^6*6250000000000^5 ≤ 3548380195131^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119572707 5000000000 3548380195131 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2844291057/10000000000 : ℝ)^6 ≤ (1105958541977/5000000000000 : ℝ)^5 := by
    have hnat : (2844291057 : ℕ)^6*5000000000000^5 ≤ 1105958541977^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2844291057 10000000000 1105958541977 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68384511/250000000 : ℝ)^6 ≤ (2110674603103/10000000000000 : ℝ)^5 := by
    have hnat : (68384511 : ℕ)^6*10000000000000^5 ≤ 2110674603103^5*250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68384511 250000000 2110674603103 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3119572707/5000000000 : ℝ), (2844291057/10000000000 : ℝ), (68384511/250000000 : ℝ)] ![(3548380195131/6250000000000 : ℝ), (1105958541977/5000000000000 : ℝ), (2110674603103/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3119572707/5000000000 : ℝ)|^6 ≤ (3548380195131/6250000000000 : ℝ)^5
        have hw : |(3119572707/5000000000 : ℝ)|=(3119572707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2844291057/10000000000 : ℝ)|^6 ≤ (1105958541977/5000000000000 : ℝ)^5
        have hw : |(2844291057/10000000000 : ℝ)|=(2844291057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68384511/250000000 : ℝ)|^6 ≤ (2110674603103/10000000000000 : ℝ)^5
        have hw : |(68384511/250000000 : ℝ)|=(68384511/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c330063 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((28899/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28899/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5873/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5873/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28141/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28141/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (41553/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (41553/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (31839/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-99238579/5000000000 : ℝ)*X 0 0+(1085397447/2000000000 : ℝ)*X 0 1+(2856034583/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1573377311/10000000000 : ℝ)*X 0 0+(1263628077/10000000000 : ℝ)*X 0 1+(8370173619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((501684719/2000000000 : ℝ)*X 1 0+(-11320353/2000000000 : ℝ)*X 1 1+(1046271711/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1254211581/5000000000 : ℝ)*X 2 0+(8370173629/10000000000 : ℝ)*X 2 1+(-56602851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3173672481/10000000000 : ℝ)*X 0 0+(890158781/1250000000 : ℝ)*X 0 1+(312110829/2500000000 : ℝ)*X 0 2+(3173672481/10000000000 : ℝ)*X 1 0+(890158781/1250000000 : ℝ)*X 1 1+(312110829/2500000000 : ℝ)*X 1 2+(3173672481/10000000000 : ℝ)*X 2 0+(890158781/1250000000 : ℝ)*X 2 1+(312110829/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-14842209/5000000000 : ℝ)*X 0 0+(244997359/1000000000 : ℝ)*X 0 1+(2106330679/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((231906097/2000000000 : ℝ)*X 1 0+(-797524727/5000000000 : ℝ)*X 1 1+(8425322221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8075397489/10000000000 : ℝ)*X 2 0+(2860715809/10000000000 : ℝ)*X 2 1+(-11312677/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7432172511/10000000000 : ℝ)*X 0 0+(1398187763/5000000000 : ℝ)*X 0 1+(1255234381/10000000000 : ℝ)*X 0 2+(7432172511/10000000000 : ℝ)*X 1 0+(1398187763/5000000000 : ℝ)*X 1 1+(1255234381/10000000000 : ℝ)*X 1 2+(7432172511/10000000000 : ℝ)*X 2 0+(1398187763/5000000000 : ℝ)*X 2 1+(1255234381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-126204349/10000000000 : ℝ)*X 0 0+(3558500973/5000000000 : ℝ)*X 0 1+(3968092471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4019018219/5000000000 : ℝ)*X 1 0+(-17975199/10000000000 : ℝ)*X 1 1+(2938828927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((464607099/5000000000 : ℝ)*X 2 0+(8560005467/10000000000 : ℝ)*X 2 1+(-404595453/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((7540067751/10000000000 : ℝ)*X 0 0+(116196919/500000000 : ℝ)*X 0 1+(327009543/2000000000 : ℝ)*X 0 2+(7540067751/10000000000 : ℝ)*X 1 0+(116196919/500000000 : ℝ)*X 1 1+(327009543/2000000000 : ℝ)*X 1 2+(7540067751/10000000000 : ℝ)*X 2 0+(116196919/500000000 : ℝ)*X 2 1+(327009543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1837/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1837/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32973286641735366404901/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1206178262693/1000000000000 : ℝ)*(base7) + (693293/500000000000 : ℝ)*(base19) + (693923/500000000000 : ℝ)*(base50) + (104677/100000000000 : ℝ)*(base60) + (1366231777767/1000000000000 : ℝ)*(major_s0_0) + (1366231777767/1000000000000 : ℝ)*(major_s0_1) + (1366231777767/1000000000000 : ℝ)*(major_s0_2) + (2536663/500000000000 : ℝ)*(sp_s0_0) + (746242557587/500000000000 : ℝ)*(sp_s0_7) + (149252452047/100000000000 : ℝ)*(sp_s0_8) + (1492526336207/1000000000000 : ℝ)*(sp_s0_9) + (1806052590481/1000000000000 : ℝ)*(sp_s0_13) + (36147707/1000000000000 : ℝ)*(sp_s0_14) + (429151/1000000000000 : ℝ)*(sp_s0_15) + (149968581947/250000000000 : ℝ)*(f.failure) + (1492526336207/1000000000000 : ℝ)*(f.sum) + (2570491483115033/5000000000000000000000000000 : ℝ)*base62 + (1970155894990447/10000000000000000000000000000 : ℝ)*base64 + (934802498990447/10000000000000000000000000000 : ℝ)*base66 + (4884193122615033/10000000000000000000000000000 : ℝ)*base68 + (23940436759863/250000000000000000000000000 : ℝ)*base71 + (3679187195990447/10000000000000000000000000000 : ℝ)*base72 + (4846561771615033/10000000000000000000000000000 : ℝ)*base74 + (3388876367615033/10000000000000000000000000000 : ℝ)*base76 + (783871111509553/5000000000000000000000000000 : ℝ)*base79 + (91/25000000000000000 : ℝ)*base87 + (91/25000000000000000 : ℝ)*base89 + (91/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58707/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58707/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22720972848793442078673/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1209690350233/1000000000000 : ℝ)*(base7) + (1214433/500000000000 : ℝ)*(base27) + (143069/1000000000000 : ℝ)*(base49) + (668794626337/500000000000 : ℝ)*(major_s0_0) + (668794626337/500000000000 : ℝ)*(major_s0_1) + (668794626337/500000000000 : ℝ)*(major_s0_2) + (235907/1000000000000 : ℝ)*(sp_s0_0) + (11159/1000000000000 : ℝ)*(sp_s0_7) + (24581429/1000000000000 : ℝ)*(sp_s0_8) + (144595485183/100000000000 : ℝ)*(sp_s0_14) + (1445930517467/1000000000000 : ℝ)*(sp_s0_15) + (90372193681/62500000000 : ℝ)*(sp_s0_16) + (1796956238633/1000000000000 : ℝ)*(sp_s0_20) + (2987537/100000000000 : ℝ)*(sp_s0_27) + (146824548159/250000000000 : ℝ)*(f.failure) + (90372193681/62500000000 : ℝ)*(f.sum) + (145711807754463/2500000000000000000000000000 : ℝ)*base62 + (360240605201817/5000000000000000000000000000 : ℝ)*base64 + (962997224798183/5000000000000000000000000000 : ℝ)*base67 + (1388441439754463/5000000000000000000000000000 : ℝ)*base68 + (9393853551093/125000000000000000000000000 : ℝ)*base71 + (732825823201817/5000000000000000000000000000 : ℝ)*base72 + (1484028136754463/5000000000000000000000000000 : ℝ)*base74 + (340108609254463/5000000000000000000000000000 : ℝ)*base76 + (889500721048183/2500000000000000000000000000 : ℝ)*base79 + (6727/25000000000000000 : ℝ)*base87 + (6727/25000000000000000 : ℝ)*base89 + (6727/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56561/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(56561/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27541024229837335471551/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301198478517/250000000000 : ℝ)*(base7) + (5976167/1000000000000 : ℝ)*(base27) + (144786688387/1000000000000 : ℝ)*(base40) + (1860141/1000000000000 : ℝ)*(base43) + (23241/125000000000 : ℝ)*(base49) + (655391250883/500000000000 : ℝ)*(major_s0_0) + (163847580203/125000000000 : ℝ)*(major_s0_1) + (655391250883/500000000000 : ℝ)*(major_s0_2) + (29197983/1000000000000 : ℝ)*(sp_s0_9) + (25456153/500000000000 : ℝ)*(sp_s0_20) + (1406707485937/1000000000000 : ℝ)*(sp_s0_21) + (1406709346079/1000000000000 : ℝ)*(sp_s0_22) + (703339143977/500000000000 : ℝ)*(sp_s0_23) + (1780265120403/1000000000000 : ℝ)*(sp_s0_27) + (575528094807/1000000000000 : ℝ)*(f.failure) + (1406709346079/1000000000000 : ℝ)*(f.sum) + (780504797283261/1000000000000000000000000000 : ℝ)*base62 + (2213141521084203/5000000000000000000000000000 : ℝ)*base64 + (44160234756323/1250000000000000000000000000 : ℝ)*base66 + (4591649144016317/5000000000000000000000000000 : ℝ)*base68 + (47357717672487/125000000000000000000000000 : ℝ)*base71 + (2978854254084203/5000000000000000000000000000 : ℝ)*base72 + (853651682099997/1250000000000000000000000000 : ℝ)*base74 + (399073705983683/5000000000000000000000000000 : ℝ)*base77 + (697791891421899/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (21329/100000000000000000 : ℝ)*base86 + (78671/100000000000000000 : ℝ)*base89 + (21329/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (1837/3125 : ℝ) ^ (95/16 : ℝ) ≤ (4265560556449147083/100000000000000000000 : ℝ) := by
    have hpowers : (1837/3125 : ℝ)^95 ≤ (4265560556449147083/100000000000000000000 : ℝ)^16 := by
      have hnat : (1837 : ℕ)^95*100000000000000000000^16 ≤ 4265560556449147083^16*3125^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1837 3125 4265560556449147083 100000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1837/3125 : ℝ)) (X := (4265560556449147083/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (104265560556449147083/100000000000000000000 : ℝ) ≤ (5035299538557763/5000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (104265560556449147083/100000000000000000000 : ℝ)^16 ≤ (5035299538557763/5000000000000000 : ℝ)^95 := by
      have hnat : (104265560556449147083 : ℕ)^16*5000000000000000^95 ≤ 5035299538557763^95*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104265560556449147083 100000000000000000000 5035299538557763 5000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5035299538557763/5000000000000000 : ℝ)) (X := (104265560556449147083/100000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (54265560556449147083/50000000000000000000 : ℝ) ≤ (1267354478424731/1250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (54265560556449147083/50000000000000000000 : ℝ)^16 ≤ (1267354478424731/1250000000000000 : ℝ)^95 := by
      have hnat : (54265560556449147083 : ℕ)^16*1250000000000000^95 ≤ 1267354478424731^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54265560556449147083 50000000000000000000 1267354478424731 1250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1267354478424731/1250000000000000 : ℝ)) (X := (54265560556449147083/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(35299538557763/2939200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(34118375141161/2939200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1837/3125 : ℝ)) (alpha := (35299538557763/2939200000000000 : ℝ)) (beta := (34118375141161/2939200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1837/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(35299538557763/2939200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(34118375141161/2939200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (58707/100000 : ℝ) ^ (95/16 : ℝ) ≤ (66132697225670099/1562500000000000000 : ℝ) := by
    have hpowers : (58707/100000 : ℝ)^95 ≤ (66132697225670099/1562500000000000000 : ℝ)^16 := by
      have hnat : (58707 : ℕ)^95*1562500000000000000^16 ≤ 66132697225670099^16*100000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58707 100000 66132697225670099 1562500000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58707/100000 : ℝ)) (X := (66132697225670099/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (1628632697225670099/1562500000000000000 : ℝ) ≤ (2517515271488587/2500000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (1628632697225670099/1562500000000000000 : ℝ)^16 ≤ (2517515271488587/2500000000000000 : ℝ)^95 := by
      have hnat : (1628632697225670099 : ℕ)^16*2500000000000000^95 ≤ 2517515271488587^95*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1628632697225670099 1562500000000000000 2517515271488587 2500000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2517515271488587/2500000000000000 : ℝ)) (X := (1628632697225670099/1562500000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (847382697225670099/781250000000000000 : ℝ) ≤ (10137795003389699/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (847382697225670099/781250000000000000 : ℝ)^16 ≤ (10137795003389699/10000000000000000 : ℝ)^95 := by
      have hnat : (847382697225670099 : ℕ)^16*10000000000000000^95 ≤ 10137795003389699^95*781250000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        847382697225670099 781250000000000000 10137795003389699 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10137795003389699/10000000000000000 : ℝ)) (X := (847382697225670099/781250000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(5838423829529/489225000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(67733917435351/5870700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (58707/100000 : ℝ)) (alpha := (5838423829529/489225000000000 : ℝ)) (beta := (67733917435351/5870700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (58707/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(5838423829529/489225000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(67733917435351/5870700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (56561/100000 : ℝ) ^ (95/16 : ℝ) ≤ (1696446476523629869/50000000000000000000 : ℝ) := by
    have hpowers : (56561/100000 : ℝ)^95 ≤ (1696446476523629869/50000000000000000000 : ℝ)^16 := by
      have hnat : (56561 : ℕ)^95*50000000000000000000^16 ≤ 1696446476523629869^16*100000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56561 100000 1696446476523629869 50000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (56561/100000 : ℝ)) (X := (1696446476523629869/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (51696446476523629869/50000000000000000000 : ℝ) ≤ (5028176814326733/5000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (51696446476523629869/50000000000000000000 : ℝ)^16 ≤ (5028176814326733/5000000000000000 : ℝ)^95 := by
      have hnat : (51696446476523629869 : ℕ)^16*5000000000000000^95 ≤ 5028176814326733^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51696446476523629869 50000000000000000000 5028176814326733 5000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028176814326733/5000000000000000 : ℝ)) (X := (51696446476523629869/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (26696446476523629869/25000000000000000000 : ℝ) ≤ (1263898731520397/1250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (26696446476523629869/25000000000000000000 : ℝ)^16 ≤ (1263898731520397/1250000000000000 : ℝ)^95 := by
      have hnat : (26696446476523629869 : ℕ)^16*1250000000000000^95 ≤ 1263898731520397^95*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26696446476523629869 25000000000000000000 1263898731520397 1250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1263898731520397/1250000000000000 : ℝ)) (X := (26696446476523629869/25000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(28176814326733/2828050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5483622350971/565610000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (56561/100000 : ℝ)) (alpha := (28176814326733/2828050000000000 : ℝ)) (beta := (5483622350971/565610000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (56561/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(28176814326733/2828050000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5483622350971/565610000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-983386633/10000000000 : ℝ)*X 0 0+(2656592363/5000000000 : ℝ)*X 0 1+(5329936349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5313124191/10000000000 : ℝ)*X 1 0+(-245710491/2500000000 : ℝ)*X 1 1+(5330385269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5325682299/10000000000 : ℝ)*X 2 0+(5327936411/10000000000 : ℝ)*X 2 1+(-484325921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((802661583/2000000000 : ℝ)*X 0 0+(250436217/625000000 : ℝ)*X 0 1+(3989074267/10000000000 : ℝ)*X 0 2+(802661583/2000000000 : ℝ)*X 1 0+(250436217/625000000 : ℝ)*X 1 1+(3989074267/10000000000 : ℝ)*X 1 2+(802661583/2000000000 : ℝ)*X 2 0+(250436217/625000000 : ℝ)*X 2 1+(3989074267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-91814401/1000000000 : ℝ)*X 0 0+(4754569291/10000000000 : ℝ)*X 0 1+(5921982669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1270243901/2500000000 : ℝ)*X 1 0+(-429991881/10000000000 : ℝ)*X 1 1+(2961216669/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((611033481/1250000000 : ℝ)*X 2 0+(1529918961/2500000000 : ℝ)*X 2 1+(-400486/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((449274499/1000000000 : ℝ)*X 0 0+(214534189/400000000 : ℝ)*X 0 1+(1985072643/10000000000 : ℝ)*X 0 2+(449274499/1000000000 : ℝ)*X 1 0+(214534189/400000000 : ℝ)*X 1 1+(1985072643/10000000000 : ℝ)*X 1 2+(449274499/1000000000 : ℝ)*X 2 0+(214534189/400000000 : ℝ)*X 2 1+(1985072643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-217931971/5000000000 : ℝ)*X 0 0+(5088264683/10000000000 : ℝ)*X 0 1+(2955940713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2384865497/5000000000 : ℝ)*X 1 0+(-455535459/5000000000 : ℝ)*X 1 1+(1182466859/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2953376941/5000000000 : ℝ)*X 2 0+(1275773123/2500000000 : ℝ)*X 2 1+(-420197363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((377845931/625000000 : ℝ)*X 0 0+(3733248881/10000000000 : ℝ)*X 0 1+(1010488919/5000000000 : ℝ)*X 0 2+(377845931/625000000 : ℝ)*X 1 0+(3733248881/10000000000 : ℝ)*X 1 1+(1010488919/5000000000 : ℝ)*X 1 2+(377845931/625000000 : ℝ)*X 2 0+(3733248881/10000000000 : ℝ)*X 2 1+(1010488919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-387722239/10000000000 : ℝ)*X 0 0+(5668486261/10000000000 : ℝ)*X 0 1+(107313059/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1188455027/2000000000 : ℝ)*X 1 0+(-47935947/1250000000 : ℝ)*X 1 1+(5088570963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1181974511/2500000000 : ℝ)*X 2 0+(5960845769/10000000000 : ℝ)*X 2 1+(-35947233/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3119572707/5000000000 : ℝ)*X 0 0+(2844291057/10000000000 : ℝ)*X 0 1+(68384511/250000000 : ℝ)*X 0 2+(3119572707/5000000000 : ℝ)*X 1 0+(2844291057/10000000000 : ℝ)*X 1 1+(68384511/250000000 : ℝ)*X 1 2+(3119572707/5000000000 : ℝ)*X 2 0+(2844291057/10000000000 : ℝ)*X 2 1+(68384511/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330063_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((28899/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28899/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (401958845917663207887827849/55342110450000000000000000000000 : ℝ) := by norm_num
    linear_combination (262491/250000000000 : ℝ)*(base50) + (44834898489/250000000000 : ℝ)*(base60) + (1398861526349/250000000000 : ℝ)*(major_s1_0) + (1398861526349/250000000000 : ℝ)*(major_s1_1) + (1398861526349/250000000000 : ℝ)*(major_s1_2) + (12824053/500000000000 : ℝ)*(sp_s1_0) + (5324567/1000000000000 : ℝ)*(sp_s1_6) + (1091752934659/125000000000 : ℝ)*(sp_s1_7) + (136469194611/15625000000 : ℝ)*(sp_s1_8) + (1091754190491/125000000000 : ℝ)*(sp_s1_9) + (2456799242397/1000000000000 : ℝ)*(sp_s1_13) + (4512173/125000000000 : ℝ)*(sp_s1_14) + (56767659/1000000000000 : ℝ)*(sp_s1_15) + (25849417/500000000000 : ℝ)*(sp_s1_23) + (2456804566963/1000000000000 : ℝ)*(f.failure) + (8734085222763/1000000000000 : ℝ)*(f.sum) + (11765053613309105293/11068422090000000000000000000000 : ℝ)*base62 + (31886099754447/565610000000000000000000000 : ℝ)*base65 + (266956756674697/733837500000000000000000000 : ℝ)*base67 + (2851559365933817/2828050000000000000000000000 : ℝ)*base68 + (3399083802145558047/41561022800000000000000000000000 : ℝ)*base71 + (516422737793971/734800000000000000000000000 : ℝ)*base72 + (689223616319407/978450000000000000000000000 : ℝ)*base74 + (121654248626673/734800000000000000000000000 : ℝ)*base76 + (1035853739913131341/3921627600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (75861/100000000000000000 : ℝ)*base86 + (75861/100000000000000000 : ℝ)*base88 + (75861/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5873/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5873/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15497761835872279624009738859/1232284326020000000000000000000000 : ℝ) := by norm_num
    linear_combination (111029/62500000000 : ℝ)*(base21) + (937679/1000000000000 : ℝ)*(base60) + (569769974283/100000000000 : ℝ)*(major_s1_0) + (569769974283/100000000000 : ℝ)*(major_s1_1) + (569769974283/100000000000 : ℝ)*(major_s1_2) + (25437509/1000000000000 : ℝ)*(sp_s1_1) + (2522093/40000000000 : ℝ)*(sp_s1_2) + (71144857/1000000000000 : ℝ)*(sp_s1_7) + (50994359/1000000000000 : ℝ)*(sp_s1_8) + (8893622856971/1000000000000 : ℝ)*(sp_s1_14) + (222340439249/25000000000 : ℝ)*(sp_s1_15) + (4446814586519/500000000000 : ℝ)*(sp_s1_16) + (2501661366603/1000000000000 : ℝ)*(sp_s1_20) + (2495317/62500000000 : ℝ)*(sp_s1_27) + (625425322919/250000000000 : ℝ)*(f.failure) + (2223423500457/250000000000 : ℝ)*(f.sum) + (373043933159759449/1844737015000000000000000000000 : ℝ)*base63 + (234314615632883/565610000000000000000000000 : ℝ)*base65 + (14545348247237/97845000000000000000000000 : ℝ)*base67 + (118302620003527/565610000000000000000000000 : ℝ)*base69 + (1163335853257573117/3324881824000000000000000000000 : ℝ)*base71 + (49434292402419/293920000000000000000000000 : ℝ)*base73 + (2648716789547/2609200000000000000000000 : ℝ)*base75 + (192257764948673/293920000000000000000000000 : ℝ)*base77 + (52189620011893769/522883680000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (21007/25000000000000000 : ℝ)*base87 + (21007/25000000000000000 : ℝ)*base89 + (21007/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28141/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28141/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (68845548132938829779962536769/3696852978060000000000000000000000 : ℝ) := by norm_num
    linear_combination (3187911/1000000000000 : ℝ)*(base15) + (113094395279/500000000000 : ℝ)*(base40) + (130531677361/25000000000 : ℝ)*(major_s1_0) + (130531677361/25000000000 : ℝ)*(major_s1_1) + (130531677361/25000000000 : ℝ)*(major_s1_2) + (35902789/500000000000 : ℝ)*(sp_s1_0) + (13046963/125000000000 : ℝ)*(sp_s1_1) + (16584901/500000000000 : ℝ)*(sp_s1_2) + (86627651/1000000000000 : ℝ)*(sp_s1_9) + (22263463/250000000000 : ℝ)*(sp_s1_20) + (8149943192597/1000000000000 : ℝ)*(sp_s1_21) + (8149907434561/1000000000000 : ℝ)*(sp_s1_22) + (4074947600361/500000000000 : ℝ)*(sp_s1_23) + (1146211964633/500000000000 : ℝ)*(sp_s1_27) + (1146256491559/500000000000 : ℝ)*(f.failure) + (326000599927/40000000000 : ℝ)*(f.sum) + (1166539029183375311/11068422090000000000000000000000 : ℝ)*base62 + (175376430410619/565610000000000000000000000 : ℝ)*base64 + (51535028688743/146767500000000000000000000 : ℝ)*base66 + (630118769969211/565610000000000000000000000 : ℝ)*base68 + (793130582298939147/4156102280000000000000000000000 : ℝ)*base71 + (65072410769859/73480000000000000000000000 : ℝ)*base72 + (40155690286733/97845000000000000000000000 : ℝ)*base74 + (11341919858741/73480000000000000000000000 : ℝ)*base76 + (105703047100860199/392162760000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (36927/50000000000000000 : ℝ)*base87 + (36927/50000000000000000 : ℝ)*base89 + (36927/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p030_positive63 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders 63) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  have ho : distinctOrders 63=![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] := by decide
  have hs : ![![true, true, true], ![true, true, true], ![true, true, true]]=(fun (_ _ : Fin 3) => true) := by decide
  have hh := collision_c330063 p hpa (by linarith only [hpb]) X (by simpa only [ho,hs] using hX)
  apply positive_chart_tailratio hX (by decide)
  intro j
  have hn := positive_chart_nonnegative hX j j
  fin_cases j
  · change 0 ≤ pair X 0 0 at hn
    change pair X 0 1 ≤ (2/5:ℝ)*pair X 0 0
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.1,hn]
  · change 0 ≤ pair X 1 1 at hn
    change pair X 1 0 ≤ (2/5:ℝ)*pair X 1 1
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.1,hn]
  · change 0 ≤ pair X 2 2 at hn
    change pair X 2 0 ≤ (2/5:ℝ)*pair X 2 2
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.2,hn]

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders 63) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_positive63 p hpa hpb X hX

#print axioms solution
