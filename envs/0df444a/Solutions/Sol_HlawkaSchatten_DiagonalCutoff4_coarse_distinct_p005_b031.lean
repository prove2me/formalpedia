-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b031
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:28:22.325407+00:00
-- url     : https://prove2.me/submissions/81b1ea52-2941-4875-8536-19baae7ac05f

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
theorem collision_support_c305071_s0_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3685309171/10000000000 : ℝ)*x 0 + (1413009287/2500000000 : ℝ)*x 1 + (222840309/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3685309171/10000000000 : ℝ)^67 ≤ (26944228225529/100000000000000 : ℝ)^51 := by
    have hnat : (3685309171 : ℕ)^67*100000000000000^51 ≤ 26944228225529^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3685309171 10000000000 26944228225529 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1413009287/2500000000 : ℝ)^67 ≤ (47256918838301/100000000000000 : ℝ)^51 := by
    have hnat : (1413009287 : ℕ)^67*100000000000000^51 ≤ 47256918838301^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413009287 2500000000 47256918838301 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222840309/625000000 : ℝ)^67 ≤ (3224856614321/12500000000000 : ℝ)^51 := by
    have hnat : (222840309 : ℕ)^67*12500000000000^51 ≤ 3224856614321^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222840309 625000000 3224856614321 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3685309171/10000000000 : ℝ), (1413009287/2500000000 : ℝ), (222840309/625000000 : ℝ)] ![(26944228225529/100000000000000 : ℝ), (47256918838301/100000000000000 : ℝ), (3224856614321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3685309171/10000000000 : ℝ)|^67 ≤ (26944228225529/100000000000000 : ℝ)^51
        have hw : |(3685309171/10000000000 : ℝ)|=(3685309171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1413009287/2500000000 : ℝ)|^67 ≤ (47256918838301/100000000000000 : ℝ)^51
        have hw : |(1413009287/2500000000 : ℝ)|=(1413009287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(222840309/625000000 : ℝ)|^67 ≤ (3224856614321/12500000000000 : ℝ)^51
        have hw : |(222840309/625000000 : ℝ)|=(222840309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (899018139/1250000000 : ℝ)*x 0 + (-1872125341/5000000000 : ℝ)*x 1 + (-352706487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899018139/1250000000 : ℝ)^67 ≤ (64856168103633/100000000000000 : ℝ)^51 := by
    have hnat : (899018139 : ℕ)^67*100000000000000^51 ≤ 64856168103633^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899018139 1250000000 64856168103633 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1872125341/5000000000 : ℝ)^67 ≤ (13755887695287/50000000000000 : ℝ)^51 := by
    have hnat : (1872125341 : ℕ)^67*50000000000000^51 ≤ 13755887695287^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872125341 5000000000 13755887695287 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352706487/2500000000 : ℝ)^67 ≤ (7632056490681/100000000000000 : ℝ)^51 := by
    have hnat : (352706487 : ℕ)^67*100000000000000^51 ≤ 7632056490681^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352706487 2500000000 7632056490681 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(899018139/1250000000 : ℝ), (-1872125341/5000000000 : ℝ), (-352706487/2500000000 : ℝ)] ![(64856168103633/100000000000000 : ℝ), (13755887695287/50000000000000 : ℝ), (7632056490681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(899018139/1250000000 : ℝ)|^67 ≤ (64856168103633/100000000000000 : ℝ)^51
        have hw : |(899018139/1250000000 : ℝ)|=(899018139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1872125341/5000000000 : ℝ)|^67 ≤ (13755887695287/50000000000000 : ℝ)^51
        have hw : |(-1872125341/5000000000 : ℝ)|=(1872125341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-352706487/2500000000 : ℝ)|^67 ≤ (7632056490681/100000000000000 : ℝ)^51
        have hw : |(-352706487/2500000000 : ℝ)|=(352706487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-13646929/1250000000 : ℝ)*x 0 + (-1020356421/5000000000 : ℝ)*x 1 + (9020978209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13646929/1250000000 : ℝ)^67 ≤ (132313665813/50000000000000 : ℝ)^51 := by
    have hnat : (13646929 : ℕ)^67*50000000000000^51 ≤ 132313665813^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13646929 1250000000 132313665813 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020356421/5000000000 : ℝ)^67 ≤ (6197447967887/50000000000000 : ℝ)^51 := by
    have hnat : (1020356421 : ℕ)^67*50000000000000^51 ≤ 6197447967887^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020356421 5000000000 6197447967887 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9020978209/10000000000 : ℝ)^67 ≤ (87340476721187/100000000000000 : ℝ)^51 := by
    have hnat : (9020978209 : ℕ)^67*100000000000000^51 ≤ 87340476721187^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9020978209 10000000000 87340476721187 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13646929/1250000000 : ℝ), (-1020356421/5000000000 : ℝ), (9020978209/10000000000 : ℝ)] ![(132313665813/50000000000000 : ℝ), (6197447967887/50000000000000 : ℝ), (87340476721187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13646929/1250000000 : ℝ)|^67 ≤ (132313665813/50000000000000 : ℝ)^51
        have hw : |(-13646929/1250000000 : ℝ)|=(13646929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1020356421/5000000000 : ℝ)|^67 ≤ (6197447967887/50000000000000 : ℝ)^51
        have hw : |(-1020356421/5000000000 : ℝ)|=(1020356421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9020978209/10000000000 : ℝ)|^67 ≤ (87340476721187/100000000000000 : ℝ)^51
        have hw : |(9020978209/10000000000 : ℝ)|=(9020978209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-935539671/2500000000 : ℝ)*x 0 + (-2929384921/5000000000 : ℝ)*x 1 + (407941539/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (935539671/2500000000 : ℝ)^67 ≤ (13745791644507/50000000000000 : ℝ)^51 := by
    have hnat : (935539671 : ℕ)^67*50000000000000^51 ≤ 13745791644507^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935539671 2500000000 13745791644507 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2929384921/5000000000 : ℝ)^67 ≤ (3096288469337/6250000000000 : ℝ)^51 := by
    have hnat : (2929384921 : ℕ)^67*6250000000000^51 ≤ 3096288469337^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2929384921 5000000000 3096288469337 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407941539/1250000000 : ℝ)^67 ≤ (1435487574697/6250000000000 : ℝ)^51 := by
    have hnat : (407941539 : ℕ)^67*6250000000000^51 ≤ 1435487574697^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407941539 1250000000 1435487574697 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-935539671/2500000000 : ℝ), (-2929384921/5000000000 : ℝ), (407941539/1250000000 : ℝ)] ![(13745791644507/50000000000000 : ℝ), (3096288469337/6250000000000 : ℝ), (1435487574697/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-935539671/2500000000 : ℝ)|^67 ≤ (13745791644507/50000000000000 : ℝ)^51
        have hw : |(-935539671/2500000000 : ℝ)|=(935539671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2929384921/5000000000 : ℝ)|^67 ≤ (3096288469337/6250000000000 : ℝ)^51
        have hw : |(-2929384921/5000000000 : ℝ)|=(2929384921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(407941539/1250000000 : ℝ)|^67 ≤ (1435487574697/6250000000000 : ℝ)^51
        have hw : |(407941539/1250000000 : ℝ)|=(407941539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1320102451/5000000000 : ℝ)*x 0 + (1778701657/2500000000 : ℝ)*x 1 + (2787724737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320102451/5000000000 : ℝ)^67 ≤ (17385637335059/100000000000000 : ℝ)^51 := by
    have hnat : (1320102451 : ℕ)^67*100000000000000^51 ≤ 17385637335059^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320102451 5000000000 17385637335059 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1778701657/2500000000 : ℝ)^67 ≤ (63941511367819/100000000000000 : ℝ)^51 := by
    have hnat : (1778701657 : ℕ)^67*100000000000000^51 ≤ 63941511367819^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778701657 2500000000 63941511367819 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2787724737/10000000000 : ℝ)^67 ≤ (9336425639643/50000000000000 : ℝ)^51 := by
    have hnat : (2787724737 : ℕ)^67*50000000000000^51 ≤ 9336425639643^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2787724737 10000000000 9336425639643 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320102451/5000000000 : ℝ), (1778701657/2500000000 : ℝ), (2787724737/10000000000 : ℝ)] ![(17385637335059/100000000000000 : ℝ), (63941511367819/100000000000000 : ℝ), (9336425639643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320102451/5000000000 : ℝ)|^67 ≤ (17385637335059/100000000000000 : ℝ)^51
        have hw : |(1320102451/5000000000 : ℝ)|=(1320102451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1778701657/2500000000 : ℝ)|^67 ≤ (63941511367819/100000000000000 : ℝ)^51
        have hw : |(1778701657/2500000000 : ℝ)|=(1778701657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2787724737/10000000000 : ℝ)|^67 ≤ (9336425639643/50000000000000 : ℝ)^51
        have hw : |(2787724737/10000000000 : ℝ)|=(2787724737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3999415719/5000000000 : ℝ)*x 0 + (-876255089/2500000000 : ℝ)*x 1 + (-43645793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3999415719/5000000000 : ℝ)^67 ≤ (74576758053683/100000000000000 : ℝ)^51 := by
    have hnat : (3999415719 : ℕ)^67*100000000000000^51 ≤ 74576758053683^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3999415719 5000000000 74576758053683 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876255089/2500000000 : ℝ)^67 ≤ (25225998318497/100000000000000 : ℝ)^51 := by
    have hnat : (876255089 : ℕ)^67*100000000000000^51 ≤ 25225998318497^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876255089 2500000000 25225998318497 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43645793/5000000000 : ℝ)^67 ≤ (197243607133/100000000000000 : ℝ)^51 := by
    have hnat : (43645793 : ℕ)^67*100000000000000^51 ≤ 197243607133^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43645793 5000000000 197243607133 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3999415719/5000000000 : ℝ), (-876255089/2500000000 : ℝ), (-43645793/5000000000 : ℝ)] ![(74576758053683/100000000000000 : ℝ), (25225998318497/100000000000000 : ℝ), (197243607133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3999415719/5000000000 : ℝ)|^67 ≤ (74576758053683/100000000000000 : ℝ)^51
        have hw : |(3999415719/5000000000 : ℝ)|=(3999415719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-876255089/2500000000 : ℝ)|^67 ≤ (25225998318497/100000000000000 : ℝ)^51
        have hw : |(-876255089/2500000000 : ℝ)|=(876255089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43645793/5000000000 : ℝ)|^67 ≤ (197243607133/100000000000000 : ℝ)^51
        have hw : |(-43645793/5000000000 : ℝ)|=(43645793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-208354379/10000000000 : ℝ)*x 0 + (-337881281/2500000000 : ℝ)*x 1 + (4699035883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208354379/10000000000 : ℝ)^67 ≤ (618540533013/100000000000000 : ℝ)^51 := by
    have hnat : (208354379 : ℕ)^67*100000000000000^51 ≤ 618540533013^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208354379 10000000000 618540533013 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337881281/2500000000 : ℝ)^67 ≤ (7213424580387/100000000000000 : ℝ)^51 := by
    have hnat : (337881281 : ℕ)^67*100000000000000^51 ≤ 7213424580387^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337881281 2500000000 7213424580387 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4699035883/5000000000 : ℝ)^67 ≤ (92168034870941/100000000000000 : ℝ)^51 := by
    have hnat : (4699035883 : ℕ)^67*100000000000000^51 ≤ 92168034870941^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4699035883 5000000000 92168034870941 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208354379/10000000000 : ℝ), (-337881281/2500000000 : ℝ), (4699035883/5000000000 : ℝ)] ![(618540533013/100000000000000 : ℝ), (7213424580387/100000000000000 : ℝ), (92168034870941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208354379/10000000000 : ℝ)|^67 ≤ (618540533013/100000000000000 : ℝ)^51
        have hw : |(-208354379/10000000000 : ℝ)|=(208354379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-337881281/2500000000 : ℝ)|^67 ≤ (7213424580387/100000000000000 : ℝ)^51
        have hw : |(-337881281/2500000000 : ℝ)|=(337881281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4699035883/5000000000 : ℝ)|^67 ≤ (92168034870941/100000000000000 : ℝ)^51
        have hw : |(4699035883/5000000000 : ℝ)|=(4699035883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-178543821/500000000 : ℝ)*x 0 + (-550215009/2000000000 : ℝ)*x 1 + (3207011543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (178543821/500000000 : ℝ)^67 ≤ (5170099216697/20000000000000 : ℝ)^51 := by
    have hnat : (178543821 : ℕ)^67*20000000000000^51 ≤ 5170099216697^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178543821 500000000 5170099216697 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550215009/2000000000 : ℝ)^67 ≤ (18351013928459/100000000000000 : ℝ)^51 := by
    have hnat : (550215009 : ℕ)^67*100000000000000^51 ≤ 18351013928459^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550215009 2000000000 18351013928459 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3207011543/5000000000 : ℝ)^67 ≤ (55798489979213/100000000000000 : ℝ)^51 := by
    have hnat : (3207011543 : ℕ)^67*100000000000000^51 ≤ 55798489979213^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3207011543 5000000000 55798489979213 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-178543821/500000000 : ℝ), (-550215009/2000000000 : ℝ), (3207011543/5000000000 : ℝ)] ![(5170099216697/20000000000000 : ℝ), (18351013928459/100000000000000 : ℝ), (55798489979213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-178543821/500000000 : ℝ)|^67 ≤ (5170099216697/20000000000000 : ℝ)^51
        have hw : |(-178543821/500000000 : ℝ)|=(178543821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-550215009/2000000000 : ℝ)|^67 ≤ (18351013928459/100000000000000 : ℝ)^51
        have hw : |(-550215009/2000000000 : ℝ)|=(550215009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3207011543/5000000000 : ℝ)|^67 ≤ (55798489979213/100000000000000 : ℝ)^51
        have hw : |(3207011543/5000000000 : ℝ)|=(3207011543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6784978881/10000000000 : ℝ)*x 0 + (1793996651/5000000000 : ℝ)*x 1 + (1114012217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6784978881/10000000000 : ℝ)^67 ≤ (15018998694197/25000000000000 : ℝ)^51 := by
    have hnat : (6784978881 : ℕ)^67*25000000000000^51 ≤ 15018998694197^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6784978881 10000000000 15018998694197 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793996651/5000000000 : ℝ)^67 ≤ (26013406711583/100000000000000 : ℝ)^51 := by
    have hnat : (1793996651 : ℕ)^67*100000000000000^51 ≤ 26013406711583^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793996651 5000000000 26013406711583 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114012217/5000000000 : ℝ)^67 ≤ (2782119699549/20000000000000 : ℝ)^51 := by
    have hnat : (1114012217 : ℕ)^67*20000000000000^51 ≤ 2782119699549^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114012217 5000000000 2782119699549 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6784978881/10000000000 : ℝ), (1793996651/5000000000 : ℝ), (1114012217/5000000000 : ℝ)] ![(15018998694197/25000000000000 : ℝ), (26013406711583/100000000000000 : ℝ), (2782119699549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6784978881/10000000000 : ℝ)|^67 ≤ (15018998694197/25000000000000 : ℝ)^51
        have hw : |(6784978881/10000000000 : ℝ)|=(6784978881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1793996651/5000000000 : ℝ)|^67 ≤ (26013406711583/100000000000000 : ℝ)^51
        have hw : |(1793996651/5000000000 : ℝ)|=(1793996651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1114012217/5000000000 : ℝ)|^67 ≤ (2782119699549/20000000000000 : ℝ)^51
        have hw : |(1114012217/5000000000 : ℝ)|=(1114012217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8861730719/10000000000 : ℝ)*x 0 + (-3758009/20000000 : ℝ)*x 1 + (-394642637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8861730719/10000000000 : ℝ)^67 ≤ (17064115253373/20000000000000 : ℝ)^51 := by
    have hnat : (8861730719 : ℕ)^67*20000000000000^51 ≤ 17064115253373^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8861730719 10000000000 17064115253373 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3758009/20000000 : ℝ)^67 ≤ (1112091367663/10000000000000 : ℝ)^51 := by
    have hnat : (3758009 : ℕ)^67*10000000000000^51 ≤ 1112091367663^51*20000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3758009 20000000 1112091367663 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394642637/5000000000 : ℝ)^67 ≤ (889627511433/25000000000000 : ℝ)^51 := by
    have hnat : (394642637 : ℕ)^67*25000000000000^51 ≤ 889627511433^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394642637 5000000000 889627511433 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8861730719/10000000000 : ℝ), (-3758009/20000000 : ℝ), (-394642637/5000000000 : ℝ)] ![(17064115253373/20000000000000 : ℝ), (1112091367663/10000000000000 : ℝ), (889627511433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8861730719/10000000000 : ℝ)|^67 ≤ (17064115253373/20000000000000 : ℝ)^51
        have hw : |(8861730719/10000000000 : ℝ)|=(8861730719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3758009/20000000 : ℝ)|^67 ≤ (1112091367663/10000000000000 : ℝ)^51
        have hw : |(-3758009/20000000 : ℝ)|=(3758009/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394642637/5000000000 : ℝ)|^67 ≤ (889627511433/25000000000000 : ℝ)^51
        have hw : |(-394642637/5000000000 : ℝ)|=(394642637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-34380173/10000000000 : ℝ)*x 0 + (-780105083/5000000000 : ℝ)*x 1 + (9325260369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34380173/10000000000 : ℝ)^67 ≤ (1449856781/2500000000000 : ℝ)^51 := by
    have hnat : (34380173 : ℕ)^67*2500000000000^51 ≤ 1449856781^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34380173 10000000000 1449856781 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (780105083/5000000000 : ℝ)^67 ≤ (4355460518419/50000000000000 : ℝ)^51 := by
    have hnat : (780105083 : ℕ)^67*50000000000000^51 ≤ 4355460518419^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780105083 5000000000 4355460518419 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9325260369/10000000000 : ℝ)^67 ≤ (91231084675203/100000000000000 : ℝ)^51 := by
    have hnat : (9325260369 : ℕ)^67*100000000000000^51 ≤ 91231084675203^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9325260369 10000000000 91231084675203 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34380173/10000000000 : ℝ), (-780105083/5000000000 : ℝ), (9325260369/10000000000 : ℝ)] ![(1449856781/2500000000000 : ℝ), (4355460518419/50000000000000 : ℝ), (91231084675203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34380173/10000000000 : ℝ)|^67 ≤ (1449856781/2500000000000 : ℝ)^51
        have hw : |(-34380173/10000000000 : ℝ)|=(34380173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-780105083/5000000000 : ℝ)|^67 ≤ (4355460518419/50000000000000 : ℝ)^51
        have hw : |(-780105083/5000000000 : ℝ)|=(780105083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9325260369/10000000000 : ℝ)|^67 ≤ (91231084675203/100000000000000 : ℝ)^51
        have hw : |(9325260369/10000000000 : ℝ)|=(9325260369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-373642023/1000000000 : ℝ)*x 0 + (-4601650347/10000000000 : ℝ)*x 1 + (928501177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (373642023/1000000000 : ℝ)^67 ≤ (5487242707657/20000000000000 : ℝ)^51 := by
    have hnat : (373642023 : ℕ)^67*20000000000000^51 ≤ 5487242707657^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373642023 1000000000 5487242707657 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4601650347/10000000000 : ℝ)^67 ≤ (36071236090657/100000000000000 : ℝ)^51 := by
    have hnat : (4601650347 : ℕ)^67*100000000000000^51 ≤ 36071236090657^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601650347 10000000000 36071236090657 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (928501177/2000000000 : ℝ)^67 ≤ (36492550359393/100000000000000 : ℝ)^51 := by
    have hnat : (928501177 : ℕ)^67*100000000000000^51 ≤ 36492550359393^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928501177 2000000000 36492550359393 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-373642023/1000000000 : ℝ), (-4601650347/10000000000 : ℝ), (928501177/2000000000 : ℝ)] ![(5487242707657/20000000000000 : ℝ), (36071236090657/100000000000000 : ℝ), (36492550359393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-373642023/1000000000 : ℝ)|^67 ≤ (5487242707657/20000000000000 : ℝ)^51
        have hw : |(-373642023/1000000000 : ℝ)|=(373642023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4601650347/10000000000 : ℝ)|^67 ≤ (36071236090657/100000000000000 : ℝ)^51
        have hw : |(-4601650347/10000000000 : ℝ)|=(4601650347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(928501177/2000000000 : ℝ)|^67 ≤ (36492550359393/100000000000000 : ℝ)^51
        have hw : |(928501177/2000000000 : ℝ)|=(928501177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1435431893/5000000000 : ℝ)*x 0 + (6146065479/10000000000 : ℝ)*x 1 + (3777771879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1435431893/5000000000 : ℝ)^67 ≤ (4851961307099/25000000000000 : ℝ)^51 := by
    have hnat : (1435431893 : ℕ)^67*25000000000000^51 ≤ 4851961307099^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435431893 5000000000 4851961307099 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6146065479/10000000000 : ℝ)^67 ≤ (52756348732819/100000000000000 : ℝ)^51 := by
    have hnat : (6146065479 : ℕ)^67*100000000000000^51 ≤ 52756348732819^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6146065479 10000000000 52756348732819 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3777771879/10000000000 : ℝ)^67 ≤ (6958951506827/25000000000000 : ℝ)^51 := by
    have hnat : (3777771879 : ℕ)^67*25000000000000^51 ≤ 6958951506827^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3777771879 10000000000 6958951506827 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1435431893/5000000000 : ℝ), (6146065479/10000000000 : ℝ), (3777771879/10000000000 : ℝ)] ![(4851961307099/25000000000000 : ℝ), (52756348732819/100000000000000 : ℝ), (6958951506827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1435431893/5000000000 : ℝ)|^67 ≤ (4851961307099/25000000000000 : ℝ)^51
        have hw : |(1435431893/5000000000 : ℝ)|=(1435431893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6146065479/10000000000 : ℝ)|^67 ≤ (52756348732819/100000000000000 : ℝ)^51
        have hw : |(6146065479/10000000000 : ℝ)|=(6146065479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3777771879/10000000000 : ℝ)|^67 ≤ (6958951506827/25000000000000 : ℝ)^51
        have hw : |(3777771879/10000000000 : ℝ)|=(3777771879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s0_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7720581199/10000000000 : ℝ)*x 0 + (-44215737/156250000 : ℝ)*x 1 + (-851209149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7720581199/10000000000 : ℝ)^67 ≤ (71187367728717/100000000000000 : ℝ)^51 := by
    have hnat : (7720581199 : ℕ)^67*100000000000000^51 ≤ 71187367728717^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7720581199 10000000000 71187367728717 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44215737/156250000 : ℝ)^67 ≤ (19044035788427/100000000000000 : ℝ)^51 := by
    have hnat : (44215737 : ℕ)^67*100000000000000^51 ≤ 19044035788427^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44215737 156250000 19044035788427 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (851209149/5000000000 : ℝ)^67 ≤ (4884298236159/50000000000000 : ℝ)^51 := by
    have hnat : (851209149 : ℕ)^67*50000000000000^51 ≤ 4884298236159^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851209149 5000000000 4884298236159 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7720581199/10000000000 : ℝ), (-44215737/156250000 : ℝ), (-851209149/5000000000 : ℝ)] ![(71187367728717/100000000000000 : ℝ), (19044035788427/100000000000000 : ℝ), (4884298236159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7720581199/10000000000 : ℝ)|^67 ≤ (71187367728717/100000000000000 : ℝ)^51
        have hw : |(7720581199/10000000000 : ℝ)|=(7720581199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44215737/156250000 : ℝ)|^67 ≤ (19044035788427/100000000000000 : ℝ)^51
        have hw : |(-44215737/156250000 : ℝ)|=(44215737/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-851209149/5000000000 : ℝ)|^67 ≤ (4884298236159/50000000000000 : ℝ)^51
        have hw : |(-851209149/5000000000 : ℝ)|=(851209149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s1_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1132663/3200000 : ℝ)*x 0 + (-33135799/80000000 : ℝ)*x 1 + (526325897/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1132663/3200000 : ℝ)^67 ≤ (25553187638283/100000000000000 : ℝ)^51 := by
    have hnat : (1132663 : ℕ)^67*100000000000000^51 ≤ 25553187638283^51*3200000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132663 3200000 25553187638283 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33135799/80000000 : ℝ)^67 ≤ (3141345342107/10000000000000 : ℝ)^51 := by
    have hnat : (33135799 : ℕ)^67*10000000000000^51 ≤ 3141345342107^51*80000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33135799 80000000 3141345342107 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526325897/1000000000 : ℝ)^67 ≤ (43033358916387/100000000000000 : ℝ)^51 := by
    have hnat : (526325897 : ℕ)^67*100000000000000^51 ≤ 43033358916387^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526325897 1000000000 43033358916387 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1132663/3200000 : ℝ), (-33135799/80000000 : ℝ), (526325897/1000000000 : ℝ)] ![(25553187638283/100000000000000 : ℝ), (3141345342107/10000000000000 : ℝ), (43033358916387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1132663/3200000 : ℝ)|^67 ≤ (25553187638283/100000000000000 : ℝ)^51
        have hw : |(-1132663/3200000 : ℝ)|=(1132663/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33135799/80000000 : ℝ)|^67 ≤ (3141345342107/10000000000000 : ℝ)^51
        have hw : |(-33135799/80000000 : ℝ)|=(33135799/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526325897/1000000000 : ℝ)|^67 ≤ (43033358916387/100000000000000 : ℝ)^51
        have hw : |(526325897/1000000000 : ℝ)|=(526325897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s1_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2150733593/5000000000 : ℝ)*x 0 + (2546912487/5000000000 : ℝ)*x 1 + (3561908663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150733593/5000000000 : ℝ)^67 ≤ (33012073767849/100000000000000 : ℝ)^51 := by
    have hnat : (2150733593 : ℕ)^67*100000000000000^51 ≤ 33012073767849^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150733593 5000000000 33012073767849 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2546912487/5000000000 : ℝ)^67 ≤ (8244536689989/20000000000000 : ℝ)^51 := by
    have hnat : (2546912487 : ℕ)^67*20000000000000^51 ≤ 8244536689989^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2546912487 5000000000 8244536689989 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3561908663/10000000000 : ℝ)^67 ≤ (12882621381611/50000000000000 : ℝ)^51 := by
    have hnat : (3561908663 : ℕ)^67*50000000000000^51 ≤ 12882621381611^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3561908663 10000000000 12882621381611 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150733593/5000000000 : ℝ), (2546912487/5000000000 : ℝ), (3561908663/10000000000 : ℝ)] ![(33012073767849/100000000000000 : ℝ), (8244536689989/20000000000000 : ℝ), (12882621381611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150733593/5000000000 : ℝ)|^67 ≤ (33012073767849/100000000000000 : ℝ)^51
        have hw : |(2150733593/5000000000 : ℝ)|=(2150733593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2546912487/5000000000 : ℝ)|^67 ≤ (8244536689989/20000000000000 : ℝ)^51
        have hw : |(2546912487/5000000000 : ℝ)|=(2546912487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3561908663/10000000000 : ℝ)|^67 ≤ (12882621381611/50000000000000 : ℝ)^51
        have hw : |(3561908663/10000000000 : ℝ)|=(3561908663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s1_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2922259221/5000000000 : ℝ)*x 0 + (-2103132391/5000000000 : ℝ)*x 1 + (-1387563591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2922259221/5000000000 : ℝ)^67 ≤ (493823627539/1000000000000 : ℝ)^51 := by
    have hnat : (2922259221 : ℕ)^67*1000000000000^51 ≤ 493823627539^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2922259221 5000000000 493823627539 1000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2103132391/5000000000 : ℝ)^67 ≤ (3205556136227/10000000000000 : ℝ)^51 := by
    have hnat : (2103132391 : ℕ)^67*10000000000000^51 ≤ 3205556136227^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103132391 5000000000 3205556136227 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1387563591/5000000000 : ℝ)^67 ≤ (145016217741/781250000000 : ℝ)^51 := by
    have hnat : (1387563591 : ℕ)^67*781250000000^51 ≤ 145016217741^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387563591 5000000000 145016217741 781250000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2922259221/5000000000 : ℝ), (-2103132391/5000000000 : ℝ), (-1387563591/5000000000 : ℝ)] ![(493823627539/1000000000000 : ℝ), (3205556136227/10000000000000 : ℝ), (145016217741/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2922259221/5000000000 : ℝ)|^67 ≤ (493823627539/1000000000000 : ℝ)^51
        have hw : |(2922259221/5000000000 : ℝ)|=(2922259221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2103132391/5000000000 : ℝ)|^67 ≤ (3205556136227/10000000000000 : ℝ)^51
        have hw : |(-2103132391/5000000000 : ℝ)|=(2103132391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1387563591/5000000000 : ℝ)|^67 ≤ (145016217741/781250000000 : ℝ)^51
        have hw : |(-1387563591/5000000000 : ℝ)|=(1387563591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305071_s1_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2264729209/10000000000 : ℝ)*x 0 + (-2725766267/10000000000 : ℝ)*x 1 + (1856863793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2264729209/10000000000 : ℝ)^67 ≤ (14212433579977/100000000000000 : ℝ)^51 := by
    have hnat : (2264729209 : ℕ)^67*100000000000000^51 ≤ 14212433579977^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264729209 10000000000 14212433579977 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725766267/10000000000 : ℝ)^67 ≤ (18129549014111/100000000000000 : ℝ)^51 := by
    have hnat : (2725766267 : ℕ)^67*100000000000000^51 ≤ 18129549014111^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725766267 10000000000 18129549014111 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1856863793/2500000000 : ℝ)^67 ≤ (67658017391983/100000000000000 : ℝ)^51 := by
    have hnat : (1856863793 : ℕ)^67*100000000000000^51 ≤ 67658017391983^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856863793 2500000000 67658017391983 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2264729209/10000000000 : ℝ), (-2725766267/10000000000 : ℝ), (1856863793/2500000000 : ℝ)] ![(14212433579977/100000000000000 : ℝ), (18129549014111/100000000000000 : ℝ), (67658017391983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2264729209/10000000000 : ℝ)|^67 ≤ (14212433579977/100000000000000 : ℝ)^51
        have hw : |(2264729209/10000000000 : ℝ)|=(2264729209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2725766267/10000000000 : ℝ)|^67 ≤ (18129549014111/100000000000000 : ℝ)^51
        have hw : |(-2725766267/10000000000 : ℝ)|=(2725766267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1856863793/2500000000 : ℝ)|^67 ≤ (67658017391983/100000000000000 : ℝ)^51
        have hw : |(1856863793/2500000000 : ℝ)|=(1856863793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305071 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3685309171/10000000000 : ℝ)*X 1 0+(1413009287/2500000000 : ℝ)*X 1 1+(222840309/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((899018139/1250000000 : ℝ)*X 2 0+(-1872125341/5000000000 : ℝ)*X 2 1+(-352706487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((-13646929/1250000000 : ℝ)*X 0 0+(-1020356421/5000000000 : ℝ)*X 0 1+(9020978209/10000000000 : ℝ)*X 0 2+(-13646929/1250000000 : ℝ)*X 1 0+(-1020356421/5000000000 : ℝ)*X 1 1+(9020978209/10000000000 : ℝ)*X 1 2+(-13646929/1250000000 : ℝ)*X 2 0+(-1020356421/5000000000 : ℝ)*X 2 1+(9020978209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-935539671/2500000000 : ℝ)*X 0 0+(-2929384921/5000000000 : ℝ)*X 0 1+(407941539/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1320102451/5000000000 : ℝ)*X 1 0+(1778701657/2500000000 : ℝ)*X 1 1+(2787724737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3999415719/5000000000 : ℝ)*X 2 0+(-876255089/2500000000 : ℝ)*X 2 1+(-43645793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-208354379/10000000000 : ℝ)*X 0 0+(-337881281/2500000000 : ℝ)*X 0 1+(4699035883/5000000000 : ℝ)*X 0 2+(-208354379/10000000000 : ℝ)*X 1 0+(-337881281/2500000000 : ℝ)*X 1 1+(4699035883/5000000000 : ℝ)*X 1 2+(-208354379/10000000000 : ℝ)*X 2 0+(-337881281/2500000000 : ℝ)*X 2 1+(4699035883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-178543821/500000000 : ℝ)*X 0 0+(-550215009/2000000000 : ℝ)*X 0 1+(3207011543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((6784978881/10000000000 : ℝ)*X 1 0+(1793996651/5000000000 : ℝ)*X 1 1+(1114012217/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8861730719/10000000000 : ℝ)*X 2 0+(-3758009/20000000 : ℝ)*X 2 1+(-394642637/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-34380173/10000000000 : ℝ)*X 0 0+(-780105083/5000000000 : ℝ)*X 0 1+(9325260369/10000000000 : ℝ)*X 0 2+(-34380173/10000000000 : ℝ)*X 1 0+(-780105083/5000000000 : ℝ)*X 1 1+(9325260369/10000000000 : ℝ)*X 1 2+(-34380173/10000000000 : ℝ)*X 2 0+(-780105083/5000000000 : ℝ)*X 2 1+(9325260369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-373642023/1000000000 : ℝ)*X 0 0+(-4601650347/10000000000 : ℝ)*X 0 1+(928501177/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1435431893/5000000000 : ℝ)*X 1 0+(6146065479/10000000000 : ℝ)*X 1 1+(3777771879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((7720581199/10000000000 : ℝ)*X 2 0+(-44215737/156250000 : ℝ)*X 2 1+(-851209149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((71237/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71237/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10233174204078459576477/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17001702941/250000000000 : ℝ)*(base1) + (92105019841/250000000000 : ℝ)*(base7) + (26250584471/200000000000 : ℝ)*(base43) + (1019245815657/1000000000000 : ℝ)*(base54) + (266997176713/500000000000 : ℝ)*(base60) + (532662051957/250000000000 : ℝ)*(major_s0_0) + (1999395285473/1000000000000 : ℝ)*(major_s0_1) + (111140239217/100000000000 : ℝ)*(major_s0_2) + (17279387/1000000000000 : ℝ)*(sp_s0_6) + (1287647215527/500000000000 : ℝ)*(sp_s0_7) + (527708108329/200000000000 : ℝ)*(sp_s0_8) + (1488041803633/1000000000000 : ℝ)*(sp_s0_9) + (168548102251/250000000000 : ℝ)*(sp_s0_13) + (96966047/500000000000 : ℝ)*(sp_s0_20) + (696618084271/500000000000 : ℝ)*(f.failure) + (527708108329/200000000000 : ℝ)*(f.sum) + (42256225836579/10000000000000000000000000000 : ℝ)*base62 + (34990037696351/1000000000000000000000000000 : ℝ)*base64 + (2641320442104983/5000000000000000000000000000 : ℝ)*base66 + (210330220740007/500000000000000000000000000 : ℝ)*base69 + (1133619935212057/5000000000000000000000000000 : ℝ)*base71 + (1163701031351429/2500000000000000000000000000 : ℝ)*base72 + (3483429341363281/10000000000000000000000000000 : ℝ)*base75 + (246067240326547/1250000000000000000000000000 : ℝ)*base76 + (459041112807841/5000000000000000000000000000 : ℝ)*base78 + (141/1562500000000000 : ℝ)*base86 + (141/1562500000000000 : ℝ)*base88 + (2843/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-18567/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-18567/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (666166523821952545203/50000000000000000000000000 : ℝ) := by norm_num
    linear_combination (486843801257/1000000000000 : ℝ)*(base1) + (271491808221/250000000000 : ℝ)*(base7) + (4388859/250000000000 : ℝ)*(base21) + (2429051/1000000000000 : ℝ)*(base40) + (1337703/1000000000000 : ℝ)*(base53) + (6633441/1000000000000 : ℝ)*(base54) + (1103296763/3906250000 : ℝ)*(base60) + (386012812567/200000000000 : ℝ)*(major_s0_0) + (386012812567/200000000000 : ℝ)*(major_s0_1) + (1930056091691/1000000000000 : ℝ)*(major_s0_2) + (2408356584701/1000000000000 : ℝ)*(sp_s0_14) + (480378195861/250000000000 : ℝ)*(sp_s0_15) + (192148993227/100000000000 : ℝ)*(sp_s0_16) + (37223809897/20000000000 : ℝ)*(sp_s0_20) + (252414739333/200000000000 : ℝ)*(f.failure) + (1921514121147/1000000000000 : ℝ)*(f.sum) + (2885267976590717/10000000000000000000000000000 : ℝ)*base63 + (1973478597055173/10000000000000000000000000000 : ℝ)*base64 + (465457568772143/1000000000000000000000000000 : ℝ)*base67 + (888891522048861/5000000000000000000000000000 : ℝ)*base69 + (7585274606333743/10000000000000000000000000000 : ℝ)*base70 + (1541268261101401/2000000000000000000000000000 : ℝ)*base73 + (1176480946301401/2000000000000000000000000000 : ℝ)*base74 + (124755727627857/1000000000000000000000000000 : ℝ)*base76 + (1088797321045687/2000000000000000000000000000 : ℝ)*base79 + (133/156250000000000 : ℝ)*base87 + (133/156250000000000 : ℝ)*base89 + (133/156250000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11161/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(11161/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (359455607218388883861/40000000000000000000000000 : ℝ) := by norm_num
    linear_combination (707644566387/250000000000 : ℝ)*(base1) + (955760753009/1000000000000 : ℝ)*(base7) + (711565769121/500000000000 : ℝ)*(base40) + (409729169729/1000000000000 : ℝ)*(base60) + (114684837023/40000000000 : ℝ)*(major_s0_0) + (114684837023/40000000000 : ℝ)*(major_s0_1) + (114684837023/40000000000 : ℝ)*(major_s0_2) + (2770427/100000000000 : ℝ)*(sp_s0_1) + (32391/250000000000 : ℝ)*(sp_s0_2) + (1298757/125000000000 : ℝ)*(sp_s0_7) + (16524659/500000000000 : ℝ)*(sp_s0_8) + (3047284692363/500000000000 : ℝ)*(sp_s0_21) + (1631970377823/500000000000 : ℝ)*(sp_s0_22) + (326400137967/100000000000 : ℝ)*(sp_s0_23) + (1874817512539/1000000000000 : ℝ)*(f.failure) + (1632000754617/500000000000 : ℝ)*(f.sum) + (57988612026303/400000000000000000000000000 : ℝ)*base62 + (332609214963631/400000000000000000000000000 : ℝ)*base65 + (91109881945033/200000000000000000000000000 : ℝ)*base66 + (109655212934967/200000000000000000000000000 : ℝ)*base68 + (38312008694713/80000000000000000000000000 : ℝ)*base71 + (151556335203631/400000000000000000000000000 : ℝ)*base72 + (70431047916369/400000000000000000000000000 : ℝ)*base74 + (47178901854967/200000000000000000000000000 : ℝ)*base77 + (67076123333697/400000000000000000000000000 : ℝ)*base78 + (1003/1562500000000000 : ℝ)*base87 + (1003/1562500000000000 : ℝ)*base89 + (1003/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (71237/100000 : ℝ) ^ (133/32 : ℝ) ≤ (12211745499766617573/50000000000000000000 : ℝ) := by
    have hpowers : (71237/100000 : ℝ)^133 ≤ (12211745499766617573/50000000000000000000 : ℝ)^32 := by
      have hnat : (71237 : ℕ)^133*50000000000000000000^32 ≤ 12211745499766617573^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71237 100000 12211745499766617573 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71237/100000 : ℝ)) (X := (12211745499766617573/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (62211745499766617573/50000000000000000000 : ℝ) ≤ (421593248376287/400000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (62211745499766617573/50000000000000000000 : ℝ)^32 ≤ (421593248376287/400000000000000 : ℝ)^133 := by
      have hnat : (62211745499766617573 : ℕ)^32*400000000000000^133 ≤ 421593248376287^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62211745499766617573 50000000000000000000 421593248376287 400000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (421593248376287/400000000000000 : ℝ)) (X := (62211745499766617573/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (37211745499766617573/25000000000000000000 : ℝ) ≤ (88034215566327/80000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (37211745499766617573/25000000000000000000 : ℝ)^32 ≤ (88034215566327/80000000000000 : ℝ)^133 := by
      have hnat : (37211745499766617573 : ℕ)^32*80000000000000^133 ≤ 88034215566327^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37211745499766617573 25000000000000000000 88034215566327 80000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (88034215566327/80000000000000 : ℝ)) (X := (37211745499766617573/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(21593248376287/284948000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4644457363837/71237000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (71237/100000 : ℝ)) (alpha := (21593248376287/284948000000000 : ℝ)) (beta := (4644457363837/71237000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (71237/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(21593248376287/284948000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4644457363837/71237000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (18567/20000 : ℝ) ^ (133/32 : ℝ) ≤ (73417894689451805247/100000000000000000000 : ℝ) := by
    have hpowers : (18567/20000 : ℝ)^133 ≤ (73417894689451805247/100000000000000000000 : ℝ)^32 := by
      have hnat : (18567 : ℕ)^133*100000000000000000000^32 ≤ 73417894689451805247^32*20000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18567 20000 73417894689451805247 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18567/20000 : ℝ)) (X := (73417894689451805247/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (173417894689451805247/100000000000000000000 : ℝ) ≤ (11416325798998291/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (173417894689451805247/100000000000000000000 : ℝ)^32 ≤ (11416325798998291/10000000000000000 : ℝ)^133 := by
      have hnat : (173417894689451805247 : ℕ)^32*10000000000000000^133 ≤ 11416325798998291^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        173417894689451805247 100000000000000000000 11416325798998291 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11416325798998291/10000000000000000 : ℝ)) (X := (173417894689451805247/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (123417894689451805247/50000000000000000000 : ℝ) ≤ (776772788834103/625000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (123417894689451805247/50000000000000000000 : ℝ)^32 ≤ (776772788834103/625000000000000 : ℝ)^133 := by
      have hnat : (123417894689451805247 : ℕ)^32*625000000000000^133 ≤ 776772788834103^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123417894689451805247 50000000000000000000 776772788834103 625000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (776772788834103/625000000000000 : ℝ)) (X := (123417894689451805247/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(472108599666097/3094500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1012038822347357/9283500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (18567/20000 : ℝ)) (alpha := (472108599666097/3094500000000000 : ℝ)) (beta := (1012038822347357/9283500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (18567/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(472108599666097/3094500000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1012038822347357/9283500000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (11161/20000 : ℝ) ^ (133/32 : ℝ) ≤ (885340076346519223/10000000000000000000 : ℝ) := by
    have hpowers : (11161/20000 : ℝ)^133 ≤ (885340076346519223/10000000000000000000 : ℝ)^32 := by
      have hnat : (11161 : ℕ)^133*10000000000000000000^32 ≤ 885340076346519223^32*20000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11161 20000 885340076346519223 10000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11161/20000 : ℝ)) (X := (885340076346519223/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (10885340076346519223/10000000000000000000 : ℝ) ≤ (5103101956675241/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (10885340076346519223/10000000000000000000 : ℝ)^32 ≤ (5103101956675241/5000000000000000 : ℝ)^133 := by
      have hnat : (10885340076346519223 : ℕ)^32*5000000000000000^133 ≤ 5103101956675241^133*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10885340076346519223 10000000000000000000 5103101956675241 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5103101956675241/5000000000000000 : ℝ)) (X := (10885340076346519223/10000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5885340076346519223/5000000000000000000 : ℝ) ≤ (5200019423220131/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (5885340076346519223/5000000000000000000 : ℝ)^32 ≤ (5200019423220131/5000000000000000 : ℝ)^133 := by
      have hnat : (5885340076346519223 : ℕ)^32*5000000000000000^133 ≤ 5200019423220131^133*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5885340076346519223 5000000000000000000 5200019423220131 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5200019423220131/5000000000000000 : ℝ)) (X := (5885340076346519223/5000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(103101956675241/2790250000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(9691746654489/279025000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (11161/20000 : ℝ)) (alpha := (103101956675241/2790250000000000 : ℝ)) (beta := (9691746654489/279025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (11161/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(103101956675241/2790250000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(9691746654489/279025000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1132663/3200000 : ℝ)*X 0 0+(-33135799/80000000 : ℝ)*X 0 1+(526325897/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2150733593/5000000000 : ℝ)*X 1 0+(2546912487/5000000000 : ℝ)*X 1 1+(3561908663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2922259221/5000000000 : ℝ)*X 2 0+(-2103132391/5000000000 : ℝ)*X 2 1+(-1387563591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2264729209/10000000000 : ℝ)*X 0 0+(-2725766267/10000000000 : ℝ)*X 0 1+(1856863793/2500000000 : ℝ)*X 0 2+(2264729209/10000000000 : ℝ)*X 1 0+(-2725766267/10000000000 : ℝ)*X 1 1+(1856863793/2500000000 : ℝ)*X 1 2+(2264729209/10000000000 : ℝ)*X 2 0+(-2725766267/10000000000 : ℝ)*X 2 1+(1856863793/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305071_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-19299/3125 : ℝ) < ((-4779/3125 : ℝ)*P 0+(-4779/3125 : ℝ)*P 1+(-4779/3125 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-19299/3125 : ℝ) < (-2515805624679773678854221461678899899/410060527972750000000000000000000000 : ℝ) := by norm_num
    linear_combination (130591992417/500000000000 : ℝ)*(base1) + (3943/250000000000 : ℝ)*(base13) + (473/100000000000 : ℝ)*(base22) + (9707/250000000000 : ℝ)*(base31) + (43974729331/125000000000 : ℝ)*(base40) + (7977/500000000000 : ℝ)*(base53) + (19237/1000000000000 : ℝ)*(base54) + (425770577141/1000000000000 : ℝ)*(base60) + (4779/3125 : ℝ)*(major_s1_0) + (4779/3125 : ℝ)*(major_s1_1) + (1529279964809/1000000000000 : ℝ)*(major_s1_2) + (2306252467841/1000000000000 : ℝ)*(sp_s1_0) + (2045068498779/1000000000000 : ℝ)*(sp_s1_1) + (1022534245383/500000000000 : ℝ)*(sp_s1_2) + (738815957101/1000000000000 : ℝ)*(sp_s1_6) + (2045068514733/1000000000000 : ℝ)*(f.sum) + (2234807964165769597/5756285750000000000000000000000 : ℝ)*base62 + (3646278753913/34878125000000000000000000 : ℝ)*base65 + (1505362286473/10315000000000000000000000 : ℝ)*base66 + (183597473539011/697562500000000000000000000 : ℝ)*base68 + (24773478884320753611/39753807850000000000000000000000 : ℝ)*base71 + (386426709206213/712370000000000000000000000 : ℝ)*base72 + (4817311548097/20630000000000000000000000 : ℝ)*base75 + (331637234359023/712370000000000000000000000 : ℝ)*base77 + (11727433360380597/18370241375000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c305072_s0_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166646969/5000000000 : ℝ)*x 0 + (-2166646969/5000000000 : ℝ)*x 1 + (-2166646969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166646969/5000000000 : ℝ), (-2166646969/5000000000 : ℝ), (-2166646969/5000000000 : ℝ)] ![(33333333323793/100000000000000 : ℝ), (33333333323793/100000000000000 : ℝ), (33333333323793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(-2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(-2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(-2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305072_s0_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2166646969/5000000000 : ℝ)*x 0 + (2166646969/5000000000 : ℝ)*x 1 + (-2166646969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166646969/5000000000 : ℝ), (2166646969/5000000000 : ℝ), (-2166646969/5000000000 : ℝ)] ![(33333333323793/100000000000000 : ℝ), (33333333323793/100000000000000 : ℝ), (33333333323793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(-2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305072_s0_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2166646969/5000000000 : ℝ)*x 0 + (-2166646969/5000000000 : ℝ)*x 1 + (2166646969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166646969/5000000000 : ℝ), (-2166646969/5000000000 : ℝ), (2166646969/5000000000 : ℝ)] ![(33333333323793/100000000000000 : ℝ), (33333333323793/100000000000000 : ℝ), (33333333323793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(-2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305072_s0_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2166646969/5000000000 : ℝ)*x 0 + (-2166646969/5000000000 : ℝ)*x 1 + (-2166646969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2166646969/5000000000 : ℝ)^67 ≤ (33333333323793/100000000000000 : ℝ)^51 := by
    have hnat : (2166646969 : ℕ)^67*100000000000000^51 ≤ 33333333323793^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166646969 5000000000 33333333323793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166646969/5000000000 : ℝ), (-2166646969/5000000000 : ℝ), (-2166646969/5000000000 : ℝ)] ![(33333333323793/100000000000000 : ℝ), (33333333323793/100000000000000 : ℝ), (33333333323793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(-2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2166646969/5000000000 : ℝ)|^67 ≤ (33333333323793/100000000000000 : ℝ)^51
        have hw : |(-2166646969/5000000000 : ℝ)|=(2166646969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305072 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base6 : ((-1 : ℝ)*T) ≤ (-1 : ℝ) := by
    linarith only [f.Tone]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2166646969/5000000000 : ℝ)*X 0 0+(-2166646969/5000000000 : ℝ)*X 0 1+(-2166646969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305072_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2166646969/5000000000 : ℝ)*X 1 0+(2166646969/5000000000 : ℝ)*X 1 1+(-2166646969/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305072_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2166646969/5000000000 : ℝ)*X 2 0+(-2166646969/5000000000 : ℝ)*X 2 1+(2166646969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305072_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2166646969/5000000000 : ℝ)*X 0 0+(-2166646969/5000000000 : ℝ)*X 0 1+(-2166646969/5000000000 : ℝ)*X 0 2+(2166646969/5000000000 : ℝ)*X 1 0+(-2166646969/5000000000 : ℝ)*X 1 1+(-2166646969/5000000000 : ℝ)*X 1 2+(2166646969/5000000000 : ℝ)*X 2 0+(-2166646969/5000000000 : ℝ)*X 2 1+(-2166646969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305072_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-19299/3125 : ℝ) < ((-4779/3125 : ℝ)*P 0+(-4779/3125 : ℝ)*P 1+(-4779/3125 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-19299/3125 : ℝ) < (-37864247206687822059/6250000000000000000 : ℝ) := by norm_num
    linear_combination (98079918327/500000000000 : ℝ)*(base6) + (92391832141/1000000000000 : ℝ)*(base39) + (92391832141/1000000000000 : ℝ)*(base49) + (92391832141/1000000000000 : ℝ)*(base59) + (4779/3125 : ℝ)*(major_s0_0) + (4779/3125 : ℝ)*(major_s0_1) + (4779/3125 : ℝ)*(major_s0_2) + (1042406564953/500000000000 : ℝ)*(sp_s0_0) + (1042406564953/500000000000 : ℝ)*(sp_s0_1) + (1042406564953/500000000000 : ℝ)*(sp_s0_2) + (401920081673/500000000000 : ℝ)*(sp_s0_6) + (1042406564953/500000000000 : ℝ)*(f.sum) + (920651/3125000000000000000 : ℝ)*base63 + (321462223/1250000000000000000000 : ℝ)*base64 + (150767577/1250000000000000000000 : ℝ)*base67 + (150767577/1250000000000000000000 : ℝ)*base68 + (920651/3125000000000000000 : ℝ)*base70 + (321462223/1250000000000000000000 : ℝ)*base72 + (321462223/1250000000000000000000 : ℝ)*base75 + (150767577/1250000000000000000000 : ℝ)*base77 + (920651/3125000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p005_b031 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (c : Fin 88) (hlo : 71 ≤ c.val) (hhi : c.val < 73)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=71 ∨ c=72 := by omega
  rcases hc with rfl|rfl
  · exact collision_c305071 p hpa (by linarith only [hpb]) X hX
  · exact collision_c305072 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (c : Fin 88) (hlo : 71 ≤ c.val) (hhi : c.val < 73)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b031 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
