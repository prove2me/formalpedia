-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_b025
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:45:00.162423+00:00
-- url     : https://prove2.me/submissions/fb569f92-b9ac-4254-a41c-979106f47fc7

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
theorem collision_support_c322046_s0_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-465133633/5000000000 : ℝ)*x 0 + (-1364673753/2500000000 : ℝ)*x 1 + (-1364673753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (465133633/5000000000 : ℝ)^21 ≤ (665023849443/12500000000000 : ℝ)^17 := by
    have hnat : (465133633 : ℕ)^21*12500000000000^17 ≤ 665023849443^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465133633 5000000000 665023849443 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364673753/2500000000 : ℝ)^21 ≤ (23669952297801/50000000000000 : ℝ)^17 := by
    have hnat : (1364673753 : ℕ)^21*50000000000000^17 ≤ 23669952297801^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364673753 2500000000 23669952297801 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364673753/2500000000 : ℝ)^21 ≤ (23669952297801/50000000000000 : ℝ)^17 := by
    have hnat : (1364673753 : ℕ)^21*50000000000000^17 ≤ 23669952297801^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364673753 2500000000 23669952297801 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-465133633/5000000000 : ℝ), (-1364673753/2500000000 : ℝ), (-1364673753/2500000000 : ℝ)] ![(665023849443/12500000000000 : ℝ), (23669952297801/50000000000000 : ℝ), (23669952297801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-465133633/5000000000 : ℝ)|^21 ≤ (665023849443/12500000000000 : ℝ)^17
        have hw : |(-465133633/5000000000 : ℝ)|=(465133633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1364673753/2500000000 : ℝ)|^21 ≤ (23669952297801/50000000000000 : ℝ)^17
        have hw : |(-1364673753/2500000000 : ℝ)|=(1364673753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1364673753/2500000000 : ℝ)|^21 ≤ (23669952297801/50000000000000 : ℝ)^17
        have hw : |(-1364673753/2500000000 : ℝ)|=(1364673753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2062796711/2500000000 : ℝ)*x 0 + (-324299119/2000000000 : ℝ)*x 1 + (-324299119/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062796711/2500000000 : ℝ)^21 ≤ (78862987796337/100000000000000 : ℝ)^17 := by
    have hnat : (2062796711 : ℕ)^21*100000000000000^17 ≤ 78862987796337^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062796711 2500000000 78862987796337 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324299119/2000000000 : ℝ)^21 ≤ (5284253047229/50000000000000 : ℝ)^17 := by
    have hnat : (324299119 : ℕ)^21*50000000000000^17 ≤ 5284253047229^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324299119 2000000000 5284253047229 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324299119/2000000000 : ℝ)^21 ≤ (5284253047229/50000000000000 : ℝ)^17 := by
    have hnat : (324299119 : ℕ)^21*50000000000000^17 ≤ 5284253047229^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324299119 2000000000 5284253047229 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2062796711/2500000000 : ℝ), (-324299119/2000000000 : ℝ), (-324299119/2000000000 : ℝ)] ![(78862987796337/100000000000000 : ℝ), (5284253047229/50000000000000 : ℝ), (5284253047229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2062796711/2500000000 : ℝ)|^21 ≤ (78862987796337/100000000000000 : ℝ)^17
        have hw : |(2062796711/2500000000 : ℝ)|=(2062796711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-324299119/2000000000 : ℝ)|^21 ≤ (5284253047229/50000000000000 : ℝ)^17
        have hw : |(-324299119/2000000000 : ℝ)|=(324299119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-324299119/2000000000 : ℝ)|^21 ≤ (5284253047229/50000000000000 : ℝ)^17
        have hw : |(-324299119/2000000000 : ℝ)|=(324299119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-931671407/10000000000 : ℝ)*x 0 + (-137316987/250000000 : ℝ)*x 1 + (-2711866591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (931671407/10000000000 : ℝ)^21 ≤ (1066022460521/20000000000000 : ℝ)^17 := by
    have hnat : (931671407 : ℕ)^21*20000000000000^17 ≤ 1066022460521^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931671407 10000000000 1066022460521 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137316987/250000000 : ℝ)^21 ≤ (2385212230579/5000000000000 : ℝ)^17 := by
    have hnat : (137316987 : ℕ)^21*5000000000000^17 ≤ 2385212230579^17*250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137316987 250000000 2385212230579 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711866591/5000000000 : ℝ)^21 ≤ (9393128615379/20000000000000 : ℝ)^17 := by
    have hnat : (2711866591 : ℕ)^21*20000000000000^17 ≤ 9393128615379^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711866591 5000000000 9393128615379 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-931671407/10000000000 : ℝ), (-137316987/250000000 : ℝ), (-2711866591/5000000000 : ℝ)] ![(1066022460521/20000000000000 : ℝ), (2385212230579/5000000000000 : ℝ), (9393128615379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-931671407/10000000000 : ℝ)|^21 ≤ (1066022460521/20000000000000 : ℝ)^17
        have hw : |(-931671407/10000000000 : ℝ)|=(931671407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137316987/250000000 : ℝ)|^21 ≤ (2385212230579/5000000000000 : ℝ)^17
        have hw : |(-137316987/250000000 : ℝ)|=(137316987/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2711866591/5000000000 : ℝ)|^21 ≤ (9393128615379/20000000000000 : ℝ)^17
        have hw : |(-2711866591/5000000000 : ℝ)|=(2711866591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1208175629/2500000000 : ℝ)*x 0 + (46997409/125000000 : ℝ)*x 1 + (-742519661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1208175629/2500000000 : ℝ)^21 ≤ (40726945712409/100000000000000 : ℝ)^17 := by
    have hnat : (1208175629 : ℕ)^21*100000000000000^17 ≤ 40726945712409^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208175629 2500000000 40726945712409 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46997409/125000000 : ℝ)^21 ≤ (29867747278521/100000000000000 : ℝ)^17 := by
    have hnat : (46997409 : ℕ)^21*100000000000000^17 ≤ 29867747278521^17*125000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46997409 125000000 29867747278521 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (742519661/2000000000 : ℝ)^21 ≤ (29405306994041/100000000000000 : ℝ)^17 := by
    have hnat : (742519661 : ℕ)^21*100000000000000^17 ≤ 29405306994041^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742519661 2000000000 29405306994041 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1208175629/2500000000 : ℝ), (46997409/125000000 : ℝ), (-742519661/2000000000 : ℝ)] ![(40726945712409/100000000000000 : ℝ), (29867747278521/100000000000000 : ℝ), (29405306994041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1208175629/2500000000 : ℝ)|^21 ≤ (40726945712409/100000000000000 : ℝ)^17
        have hw : |(1208175629/2500000000 : ℝ)|=(1208175629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46997409/125000000 : ℝ)|^21 ≤ (29867747278521/100000000000000 : ℝ)^17
        have hw : |(46997409/125000000 : ℝ)|=(46997409/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-742519661/2000000000 : ℝ)|^21 ≤ (29405306994041/100000000000000 : ℝ)^17
        have hw : |(-742519661/2000000000 : ℝ)|=(742519661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1208175657/2500000000 : ℝ)*x 0 + (-3685704943/10000000000 : ℝ)*x 1 + (946640219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1208175657/2500000000 : ℝ)^21 ≤ (40726946878359/100000000000000 : ℝ)^17 := by
    have hnat : (1208175657 : ℕ)^21*100000000000000^17 ≤ 40726946878359^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208175657 2500000000 40726946878359 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3685704943/10000000000 : ℝ)^21 ≤ (1821400373363/6250000000000 : ℝ)^17 := by
    have hnat : (3685704943 : ℕ)^21*6250000000000^17 ≤ 1821400373363^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3685704943 10000000000 1821400373363 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (946640219/2500000000 : ℝ)^21 ≤ (3013064713419/10000000000000 : ℝ)^17 := by
    have hnat : (946640219 : ℕ)^21*10000000000000^17 ≤ 3013064713419^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946640219 2500000000 3013064713419 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1208175657/2500000000 : ℝ), (-3685704943/10000000000 : ℝ), (946640219/2500000000 : ℝ)] ![(40726946878359/100000000000000 : ℝ), (1821400373363/6250000000000 : ℝ), (3013064713419/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1208175657/2500000000 : ℝ)|^21 ≤ (40726946878359/100000000000000 : ℝ)^17
        have hw : |(1208175657/2500000000 : ℝ)|=(1208175657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3685704943/10000000000 : ℝ)|^21 ≤ (1821400373363/6250000000000 : ℝ)^17
        have hw : |(-3685704943/10000000000 : ℝ)|=(3685704943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(946640219/2500000000 : ℝ)|^21 ≤ (3013064713419/10000000000000 : ℝ)^17
        have hw : |(946640219/2500000000 : ℝ)|=(946640219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1650838449/2000000000 : ℝ)*x 0 + (-1597401141/10000000000 : ℝ)*x 1 + (-820556279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1650838449/2000000000 : ℝ)^21 ≤ (308197160447/390625000000 : ℝ)^17 := by
    have hnat : (1650838449 : ℕ)^21*390625000000^17 ≤ 308197160447^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650838449 2000000000 308197160447 390625000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1597401141/10000000000 : ℝ)^21 ≤ (10374853861499/100000000000000 : ℝ)^17 := by
    have hnat : (1597401141 : ℕ)^21*100000000000000^17 ≤ 10374853861499^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1597401141 10000000000 10374853861499 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (820556279/5000000000 : ℝ)^21 ≤ (5363336528531/50000000000000 : ℝ)^17 := by
    have hnat : (820556279 : ℕ)^21*50000000000000^17 ≤ 5363336528531^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820556279 5000000000 5363336528531 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1650838449/2000000000 : ℝ), (-1597401141/10000000000 : ℝ), (-820556279/5000000000 : ℝ)] ![(308197160447/390625000000 : ℝ), (10374853861499/100000000000000 : ℝ), (5363336528531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1650838449/2000000000 : ℝ)|^21 ≤ (308197160447/390625000000 : ℝ)^17
        have hw : |(1650838449/2000000000 : ℝ)|=(1650838449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1597401141/10000000000 : ℝ)|^21 ≤ (10374853861499/100000000000000 : ℝ)^17
        have hw : |(-1597401141/10000000000 : ℝ)|=(1597401141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-820556279/5000000000 : ℝ)|^21 ≤ (5363336528531/50000000000000 : ℝ)^17
        have hw : |(-820556279/5000000000 : ℝ)|=(820556279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-671040761/10000000000 : ℝ)*x 0 + (-21503871/39062500 : ℝ)*x 1 + (-5576939437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671040761/10000000000 : ℝ)^21 ≤ (710754822239/20000000000000 : ℝ)^17 := by
    have hnat : (671040761 : ℕ)^21*20000000000000^17 ≤ 710754822239^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671040761 10000000000 710754822239 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21503871/39062500 : ℝ)^21 ≤ (11959091141133/25000000000000 : ℝ)^17 := by
    have hnat : (21503871 : ℕ)^21*25000000000000^17 ≤ 11959091141133^17*39062500^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21503871 39062500 11959091141133 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5576939437/10000000000 : ℝ)^21 ≤ (1519058165977/3125000000000 : ℝ)^17 := by
    have hnat : (5576939437 : ℕ)^21*3125000000000^17 ≤ 1519058165977^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5576939437 10000000000 1519058165977 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-671040761/10000000000 : ℝ), (-21503871/39062500 : ℝ), (-5576939437/10000000000 : ℝ)] ![(710754822239/20000000000000 : ℝ), (11959091141133/25000000000000 : ℝ), (1519058165977/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-671040761/10000000000 : ℝ)|^21 ≤ (710754822239/20000000000000 : ℝ)^17
        have hw : |(-671040761/10000000000 : ℝ)|=(671040761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21503871/39062500 : ℝ)|^21 ≤ (11959091141133/25000000000000 : ℝ)^17
        have hw : |(-21503871/39062500 : ℝ)|=(21503871/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5576939437/10000000000 : ℝ)|^21 ≤ (1519058165977/3125000000000 : ℝ)^17
        have hw : |(-5576939437/10000000000 : ℝ)|=(5576939437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2367932551/5000000000 : ℝ)*x 0 + (188142071/500000000 : ℝ)*x 1 + (-1906010273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2367932551/5000000000 : ℝ)^21 ≤ (39721230473333/100000000000000 : ℝ)^17 := by
    have hnat : (2367932551 : ℕ)^21*100000000000000^17 ≤ 39721230473333^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2367932551 5000000000 39721230473333 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188142071/500000000 : ℝ)^21 ≤ (29897667516881/100000000000000 : ℝ)^17 := by
    have hnat : (188142071 : ℕ)^21*100000000000000^17 ≤ 29897667516881^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188142071 500000000 29897667516881 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1906010273/5000000000 : ℝ)^21 ≤ (6076220400051/20000000000000 : ℝ)^17 := by
    have hnat : (1906010273 : ℕ)^21*20000000000000^17 ≤ 6076220400051^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906010273 5000000000 6076220400051 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2367932551/5000000000 : ℝ), (188142071/500000000 : ℝ), (-1906010273/5000000000 : ℝ)] ![(39721230473333/100000000000000 : ℝ), (29897667516881/100000000000000 : ℝ), (6076220400051/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2367932551/5000000000 : ℝ)|^21 ≤ (39721230473333/100000000000000 : ℝ)^17
        have hw : |(2367932551/5000000000 : ℝ)|=(2367932551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(188142071/500000000 : ℝ)|^21 ≤ (29897667516881/100000000000000 : ℝ)^17
        have hw : |(188142071/500000000 : ℝ)|=(188142071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1906010273/5000000000 : ℝ)|^21 ≤ (6076220400051/20000000000000 : ℝ)^17
        have hw : |(-1906010273/5000000000 : ℝ)|=(1906010273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2550013749/5000000000 : ℝ)*x 0 + (-356929783/1000000000 : ℝ)*x 1 + (903986851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2550013749/5000000000 : ℝ)^21 ≤ (43527733235349/100000000000000 : ℝ)^17 := by
    have hnat : (2550013749 : ℕ)^21*100000000000000^17 ≤ 43527733235349^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2550013749 5000000000 43527733235349 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (356929783/1000000000 : ℝ)^21 ≤ (28009680168661/100000000000000 : ℝ)^17 := by
    have hnat : (356929783 : ℕ)^21*100000000000000^17 ≤ 28009680168661^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356929783 1000000000 28009680168661 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903986851/2500000000 : ℝ)^21 ≤ (28462586582669/100000000000000 : ℝ)^17 := by
    have hnat : (903986851 : ℕ)^21*100000000000000^17 ≤ 28462586582669^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903986851 2500000000 28462586582669 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2550013749/5000000000 : ℝ), (-356929783/1000000000 : ℝ), (903986851/2500000000 : ℝ)] ![(43527733235349/100000000000000 : ℝ), (28009680168661/100000000000000 : ℝ), (28462586582669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2550013749/5000000000 : ℝ)|^21 ≤ (43527733235349/100000000000000 : ℝ)^17
        have hw : |(2550013749/5000000000 : ℝ)|=(2550013749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-356929783/1000000000 : ℝ)|^21 ≤ (28009680168661/100000000000000 : ℝ)^17
        have hw : |(-356929783/1000000000 : ℝ)|=(356929783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903986851/2500000000 : ℝ)|^21 ≤ (28462586582669/100000000000000 : ℝ)^17
        have hw : |(903986851/2500000000 : ℝ)|=(903986851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_19 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8550272041/10000000000 : ℝ)*x 0 + (-1388419323/10000000000 : ℝ)*x 1 + (-1406565517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8550272041/10000000000 : ℝ)^21 ≤ (82409107562279/100000000000000 : ℝ)^17 := by
    have hnat : (8550272041 : ℕ)^21*100000000000000^17 ≤ 82409107562279^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8550272041 10000000000 82409107562279 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1388419323/10000000000 : ℝ)^21 ≤ (8724906910463/100000000000000 : ℝ)^17 := by
    have hnat : (1388419323 : ℕ)^21*100000000000000^17 ≤ 8724906910463^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388419323 10000000000 8724906910463 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1406565517/10000000000 : ℝ)^21 ≤ (1108248188329/12500000000000 : ℝ)^17 := by
    have hnat : (1406565517 : ℕ)^21*12500000000000^17 ≤ 1108248188329^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406565517 10000000000 1108248188329 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8550272041/10000000000 : ℝ), (-1388419323/10000000000 : ℝ), (-1406565517/10000000000 : ℝ)] ![(82409107562279/100000000000000 : ℝ), (8724906910463/100000000000000 : ℝ), (1108248188329/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8550272041/10000000000 : ℝ)|^21 ≤ (82409107562279/100000000000000 : ℝ)^17
        have hw : |(8550272041/10000000000 : ℝ)|=(8550272041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1388419323/10000000000 : ℝ)|^21 ≤ (8724906910463/100000000000000 : ℝ)^17
        have hw : |(-1388419323/10000000000 : ℝ)|=(1388419323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1406565517/10000000000 : ℝ)|^21 ≤ (1108248188329/12500000000000 : ℝ)^17
        have hw : |(-1406565517/10000000000 : ℝ)|=(1406565517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-671040759/10000000000 : ℝ)*x 0 + (-1115387877/2000000000 : ℝ)*x 1 + (-550499103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671040759/10000000000 : ℝ)^21 ≤ (3553774098111/100000000000000 : ℝ)^17 := by
    have hnat : (671040759 : ℕ)^21*100000000000000^17 ≤ 3553774098111^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671040759 10000000000 3553774098111 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115387877/2000000000 : ℝ)^21 ≤ (388878886011/800000000000 : ℝ)^17 := by
    have hnat : (1115387877 : ℕ)^21*800000000000^17 ≤ 388878886011^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115387877 2000000000 388878886011 800000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550499103/1000000000 : ℝ)^21 ≤ (23918182572091/50000000000000 : ℝ)^17 := by
    have hnat : (550499103 : ℕ)^21*50000000000000^17 ≤ 23918182572091^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550499103 1000000000 23918182572091 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-671040759/10000000000 : ℝ), (-1115387877/2000000000 : ℝ), (-550499103/1000000000 : ℝ)] ![(3553774098111/100000000000000 : ℝ), (388878886011/800000000000 : ℝ), (23918182572091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-671040759/10000000000 : ℝ)|^21 ≤ (3553774098111/100000000000000 : ℝ)^17
        have hw : |(-671040759/10000000000 : ℝ)|=(671040759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115387877/2000000000 : ℝ)|^21 ≤ (388878886011/800000000000 : ℝ)^17
        have hw : |(-1115387877/2000000000 : ℝ)|=(1115387877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550499103/1000000000 : ℝ)|^21 ≤ (23918182572091/50000000000000 : ℝ)^17
        have hw : |(-550499103/1000000000 : ℝ)|=(550499103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (318751719/625000000 : ℝ)*x 0 + (1807973683/5000000000 : ℝ)*x 1 + (-3569297861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (318751719/625000000 : ℝ)^21 ≤ (43527733298607/100000000000000 : ℝ)^17 := by
    have hnat : (318751719 : ℕ)^21*100000000000000^17 ≤ 43527733298607^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318751719 625000000 43527733298607 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1807973683/5000000000 : ℝ)^21 ≤ (3557823276647/12500000000000 : ℝ)^17 := by
    have hnat : (1807973683 : ℕ)^21*12500000000000^17 ≤ 3557823276647^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1807973683 5000000000 3557823276647 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3569297861/10000000000 : ℝ)^21 ≤ (2800968046917/10000000000000 : ℝ)^17 := by
    have hnat : (3569297861 : ℕ)^21*10000000000000^17 ≤ 2800968046917^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3569297861 10000000000 2800968046917 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(318751719/625000000 : ℝ), (1807973683/5000000000 : ℝ), (-3569297861/10000000000 : ℝ)] ![(43527733298607/100000000000000 : ℝ), (3557823276647/12500000000000 : ℝ), (2800968046917/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(318751719/625000000 : ℝ)|^21 ≤ (43527733298607/100000000000000 : ℝ)^17
        have hw : |(318751719/625000000 : ℝ)|=(318751719/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1807973683/5000000000 : ℝ)|^21 ≤ (3557823276647/12500000000000 : ℝ)^17
        have hw : |(1807973683/5000000000 : ℝ)|=(1807973683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3569297861/10000000000 : ℝ)|^21 ≤ (2800968046917/10000000000000 : ℝ)^17
        have hw : |(-3569297861/10000000000 : ℝ)|=(3569297861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2367932517/5000000000 : ℝ)*x 0 + (-1906010273/5000000000 : ℝ)*x 1 + (3762841491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2367932517/5000000000 : ℝ)^21 ≤ (39721229768797/100000000000000 : ℝ)^17 := by
    have hnat : (2367932517 : ℕ)^21*100000000000000^17 ≤ 39721229768797^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2367932517 5000000000 39721229768797 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1906010273/5000000000 : ℝ)^21 ≤ (6076220400051/20000000000000 : ℝ)^17 := by
    have hnat : (1906010273 : ℕ)^21*20000000000000^17 ≤ 6076220400051^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906010273 5000000000 6076220400051 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3762841491/10000000000 : ℝ)^21 ≤ (29897668213749/100000000000000 : ℝ)^17 := by
    have hnat : (3762841491 : ℕ)^21*100000000000000^17 ≤ 29897668213749^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3762841491 10000000000 29897668213749 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2367932517/5000000000 : ℝ), (-1906010273/5000000000 : ℝ), (3762841491/10000000000 : ℝ)] ![(39721229768797/100000000000000 : ℝ), (6076220400051/20000000000000 : ℝ), (29897668213749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2367932517/5000000000 : ℝ)|^21 ≤ (39721229768797/100000000000000 : ℝ)^17
        have hw : |(2367932517/5000000000 : ℝ)|=(2367932517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1906010273/5000000000 : ℝ)|^21 ≤ (6076220400051/20000000000000 : ℝ)^17
        have hw : |(-1906010273/5000000000 : ℝ)|=(1906010273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3762841491/10000000000 : ℝ)|^21 ≤ (29897668213749/100000000000000 : ℝ)^17
        have hw : |(3762841491/10000000000 : ℝ)|=(3762841491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s0_25 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8550272021/10000000000 : ℝ)*x 0 + (-1406565519/10000000000 : ℝ)*x 1 + (-173552419/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8550272021/10000000000 : ℝ)^21 ≤ (82409107324159/100000000000000 : ℝ)^17 := by
    have hnat : (8550272021 : ℕ)^21*100000000000000^17 ≤ 82409107324159^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8550272021 10000000000 82409107324159 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1406565519/10000000000 : ℝ)^21 ≤ (1773197104441/20000000000000 : ℝ)^17 := by
    have hnat : (1406565519 : ℕ)^21*20000000000000^17 ≤ 1773197104441^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406565519 10000000000 1773197104441 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173552419/1250000000 : ℝ)^21 ≤ (436245356779/5000000000000 : ℝ)^17 := by
    have hnat : (173552419 : ℕ)^21*5000000000000^17 ≤ 436245356779^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173552419 1250000000 436245356779 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8550272021/10000000000 : ℝ), (-1406565519/10000000000 : ℝ), (-173552419/1250000000 : ℝ)] ![(82409107324159/100000000000000 : ℝ), (1773197104441/20000000000000 : ℝ), (436245356779/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8550272021/10000000000 : ℝ)|^21 ≤ (82409107324159/100000000000000 : ℝ)^17
        have hw : |(8550272021/10000000000 : ℝ)|=(8550272021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1406565519/10000000000 : ℝ)|^21 ≤ (1773197104441/20000000000000 : ℝ)^17
        have hw : |(-1406565519/10000000000 : ℝ)|=(1406565519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173552419/1250000000 : ℝ)|^21 ≤ (436245356779/5000000000000 : ℝ)^17
        have hw : |(-173552419/1250000000 : ℝ)|=(173552419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-72937061/312500000 : ℝ)*x 0 + (-153975849/312500000 : ℝ)*x 1 + (-153975849/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72937061/312500000 : ℝ)^21 ≤ (16573547226491/100000000000000 : ℝ)^17 := by
    have hnat : (72937061 : ℕ)^21*100000000000000^17 ≤ 16573547226491^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72937061 312500000 16573547226491 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153975849/312500000 : ℝ)^21 ≤ (41713226378023/100000000000000 : ℝ)^17 := by
    have hnat : (153975849 : ℕ)^21*100000000000000^17 ≤ 41713226378023^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153975849 312500000 41713226378023 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153975849/312500000 : ℝ)^21 ≤ (41713226378023/100000000000000 : ℝ)^17 := by
    have hnat : (153975849 : ℕ)^21*100000000000000^17 ≤ 41713226378023^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153975849 312500000 41713226378023 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-72937061/312500000 : ℝ), (-153975849/312500000 : ℝ), (-153975849/312500000 : ℝ)] ![(16573547226491/100000000000000 : ℝ), (41713226378023/100000000000000 : ℝ), (41713226378023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-72937061/312500000 : ℝ)|^21 ≤ (16573547226491/100000000000000 : ℝ)^17
        have hw : |(-72937061/312500000 : ℝ)|=(72937061/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-153975849/312500000 : ℝ)|^21 ≤ (41713226378023/100000000000000 : ℝ)^17
        have hw : |(-153975849/312500000 : ℝ)|=(153975849/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153975849/312500000 : ℝ)|^21 ≤ (41713226378023/100000000000000 : ℝ)^17
        have hw : |(-153975849/312500000 : ℝ)|=(153975849/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (112844143/250000000 : ℝ)*x 0 + (390342661/1000000000 : ℝ)*x 1 + (-390342661/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112844143/250000000 : ℝ)^21 ≤ (1497318075481/4000000000000 : ℝ)^17 := by
    have hnat : (112844143 : ℕ)^21*4000000000000^17 ≤ 1497318075481^17*250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112844143 250000000 1497318075481 4000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390342661/1000000000 : ℝ)^21 ≤ (31283524045513/100000000000000 : ℝ)^17 := by
    have hnat : (390342661 : ℕ)^21*100000000000000^17 ≤ 31283524045513^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390342661 1000000000 31283524045513 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (390342661/1000000000 : ℝ)^21 ≤ (31283524045513/100000000000000 : ℝ)^17 := by
    have hnat : (390342661 : ℕ)^21*100000000000000^17 ≤ 31283524045513^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390342661 1000000000 31283524045513 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112844143/250000000 : ℝ), (390342661/1000000000 : ℝ), (-390342661/1000000000 : ℝ)] ![(1497318075481/4000000000000 : ℝ), (31283524045513/100000000000000 : ℝ), (31283524045513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112844143/250000000 : ℝ)|^21 ≤ (1497318075481/4000000000000 : ℝ)^17
        have hw : |(112844143/250000000 : ℝ)|=(112844143/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(390342661/1000000000 : ℝ)|^21 ≤ (31283524045513/100000000000000 : ℝ)^17
        have hw : |(390342661/1000000000 : ℝ)|=(390342661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-390342661/1000000000 : ℝ)|^21 ≤ (31283524045513/100000000000000 : ℝ)^17
        have hw : |(-390342661/1000000000 : ℝ)|=(390342661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4513765719/10000000000 : ℝ)*x 0 + (-3903426611/10000000000 : ℝ)*x 1 + (3903426611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4513765719/10000000000 : ℝ)^21 ≤ (37432951876781/100000000000000 : ℝ)^17 := by
    have hnat : (4513765719 : ℕ)^21*100000000000000^17 ≤ 37432951876781^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513765719 10000000000 37432951876781 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3903426611/10000000000 : ℝ)^21 ≤ (31283524055413/100000000000000 : ℝ)^17 := by
    have hnat : (3903426611 : ℕ)^21*100000000000000^17 ≤ 31283524055413^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3903426611 10000000000 31283524055413 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3903426611/10000000000 : ℝ)^21 ≤ (31283524055413/100000000000000 : ℝ)^17 := by
    have hnat : (3903426611 : ℕ)^21*100000000000000^17 ≤ 31283524055413^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3903426611 10000000000 31283524055413 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4513765719/10000000000 : ℝ), (-3903426611/10000000000 : ℝ), (3903426611/10000000000 : ℝ)] ![(37432951876781/100000000000000 : ℝ), (31283524055413/100000000000000 : ℝ), (31283524055413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4513765719/10000000000 : ℝ)|^21 ≤ (37432951876781/100000000000000 : ℝ)^17
        have hw : |(4513765719/10000000000 : ℝ)|=(4513765719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3903426611/10000000000 : ℝ)|^21 ≤ (31283524055413/100000000000000 : ℝ)^17
        have hw : |(-3903426611/10000000000 : ℝ)|=(3903426611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3903426611/10000000000 : ℝ)|^21 ≤ (31283524055413/100000000000000 : ℝ)^17
        have hw : |(3903426611/10000000000 : ℝ)|=(3903426611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322046_s1_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1648732953/2500000000 : ℝ)*x 0 + (-545740627/2000000000 : ℝ)*x 1 + (-545740627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1648732953/2500000000 : ℝ)^21 ≤ (59795920916549/100000000000000 : ℝ)^17 := by
    have hnat : (1648732953 : ℕ)^21*100000000000000^17 ≤ 59795920916549^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1648732953 2500000000 59795920916549 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545740627/2000000000 : ℝ)^21 ≤ (20102039533537/100000000000000 : ℝ)^17 := by
    have hnat : (545740627 : ℕ)^21*100000000000000^17 ≤ 20102039533537^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545740627 2000000000 20102039533537 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545740627/2000000000 : ℝ)^21 ≤ (20102039533537/100000000000000 : ℝ)^17 := by
    have hnat : (545740627 : ℕ)^21*100000000000000^17 ≤ 20102039533537^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545740627 2000000000 20102039533537 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1648732953/2500000000 : ℝ), (-545740627/2000000000 : ℝ), (-545740627/2000000000 : ℝ)] ![(59795920916549/100000000000000 : ℝ), (20102039533537/100000000000000 : ℝ), (20102039533537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1648732953/2500000000 : ℝ)|^21 ≤ (59795920916549/100000000000000 : ℝ)^17
        have hw : |(1648732953/2500000000 : ℝ)|=(1648732953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-545740627/2000000000 : ℝ)|^21 ≤ (20102039533537/100000000000000 : ℝ)^17
        have hw : |(-545740627/2000000000 : ℝ)|=(545740627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-545740627/2000000000 : ℝ)|^21 ≤ (20102039533537/100000000000000 : ℝ)^17
        have hw : |(-545740627/2000000000 : ℝ)|=(545740627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322046 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-465133633/5000000000 : ℝ)*X 0 0+(-1364673753/2500000000 : ℝ)*X 0 1+(-1364673753/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2062796711/2500000000 : ℝ)*X 0 0+(-324299119/2000000000 : ℝ)*X 0 1+(-324299119/2000000000 : ℝ)*X 0 2+(2062796711/2500000000 : ℝ)*X 1 0+(-324299119/2000000000 : ℝ)*X 1 1+(-324299119/2000000000 : ℝ)*X 1 2+(2062796711/2500000000 : ℝ)*X 2 0+(-324299119/2000000000 : ℝ)*X 2 1+(-324299119/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-931671407/10000000000 : ℝ)*X 0 0+(-137316987/250000000 : ℝ)*X 0 1+(-2711866591/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1208175629/2500000000 : ℝ)*X 1 0+(46997409/125000000 : ℝ)*X 1 1+(-742519661/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1208175657/2500000000 : ℝ)*X 2 0+(-3685704943/10000000000 : ℝ)*X 2 1+(946640219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1650838449/2000000000 : ℝ)*X 0 0+(-1597401141/10000000000 : ℝ)*X 0 1+(-820556279/5000000000 : ℝ)*X 0 2+(1650838449/2000000000 : ℝ)*X 1 0+(-1597401141/10000000000 : ℝ)*X 1 1+(-820556279/5000000000 : ℝ)*X 1 2+(1650838449/2000000000 : ℝ)*X 2 0+(-1597401141/10000000000 : ℝ)*X 2 1+(-820556279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-671040761/10000000000 : ℝ)*X 0 0+(-21503871/39062500 : ℝ)*X 0 1+(-5576939437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2367932551/5000000000 : ℝ)*X 1 0+(188142071/500000000 : ℝ)*X 1 1+(-1906010273/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2550013749/5000000000 : ℝ)*X 2 0+(-356929783/1000000000 : ℝ)*X 2 1+(903986851/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((8550272041/10000000000 : ℝ)*X 0 0+(-1388419323/10000000000 : ℝ)*X 0 1+(-1406565517/10000000000 : ℝ)*X 0 2+(8550272041/10000000000 : ℝ)*X 1 0+(-1388419323/10000000000 : ℝ)*X 1 1+(-1406565517/10000000000 : ℝ)*X 1 2+(8550272041/10000000000 : ℝ)*X 2 0+(-1388419323/10000000000 : ℝ)*X 2 1+(-1406565517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-671040759/10000000000 : ℝ)*X 0 0+(-1115387877/2000000000 : ℝ)*X 0 1+(-550499103/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((318751719/625000000 : ℝ)*X 1 0+(1807973683/5000000000 : ℝ)*X 1 1+(-3569297861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2367932517/5000000000 : ℝ)*X 2 0+(-1906010273/5000000000 : ℝ)*X 2 1+(3762841491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((8550272021/10000000000 : ℝ)*X 0 0+(-1406565519/10000000000 : ℝ)*X 0 1+(-173552419/1250000000 : ℝ)*X 0 2+(8550272021/10000000000 : ℝ)*X 1 0+(-1406565519/10000000000 : ℝ)*X 1 1+(-173552419/1250000000 : ℝ)*X 1 2+(8550272021/10000000000 : ℝ)*X 2 0+(-1406565519/10000000000 : ℝ)*X 2 1+(-173552419/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((439/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(439/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23874427309535051971551/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1195898478679/1000000000000 : ℝ)*(base39) + (37575311183/500000000000 : ℝ)*(base49) + (2000289407/50000000000 : ℝ)*(base59) + (4420002008549/1000000000000 : ℝ)*(major_s0_0) + (4420002008549/1000000000000 : ℝ)*(major_s0_1) + (4420002008549/1000000000000 : ℝ)*(major_s0_2) + (1408281897/1000000000000 : ℝ)*(sp_s0_0) + (176775751/100000000000 : ℝ)*(sp_s0_6) + (3274158701859/500000000000 : ℝ)*(sp_s0_7) + (6549376383337/1000000000000 : ℝ)*(sp_s0_8) + (6549368808733/1000000000000 : ℝ)*(sp_s0_9) + (228850739071/100000000000 : ℝ)*(sp_s0_13) + (174651139/500000000000 : ℝ)*(sp_s0_15) + (356876881/1000000000000 : ℝ)*(sp_s0_22) + (114513757411/50000000000 : ℝ)*(f.failure) + (1309945137123/200000000000 : ℝ)*(f.sum) + (314843368068717/1250000000000000000000000000 : ℝ)*base62 + (530639882696923/2000000000000000000000000000 : ℝ)*base65 + (2046479903896923/2000000000000000000000000000 : ℝ)*base67 + (1869365082318717/2500000000000000000000000000 : ℝ)*base68 + (4652106081790253/10000000000000000000000000000 : ℝ)*base70 + (931775730496923/2000000000000000000000000000 : ℝ)*base73 + (679277839818717/2500000000000000000000000000 : ℝ)*base74 + (199373278431283/2500000000000000000000000000 : ℝ)*base77 + (676655784996923/1000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (389/500000000000000 : ℝ)*base87 + (389/500000000000000 : ℝ)*base89 + (389/500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5977/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-5977/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1632322401580749633657/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1888065040809/200000000000 : ℝ)*(base39) + (447402958397/100000000000 : ℝ)*(base40) + (59803035523/500000000000 : ℝ)*(base49) + (23880073171/250000000000 : ℝ)*(base59) + (1158246993923/62500000000 : ℝ)*(major_s0_0) + (1158246993923/62500000000 : ℝ)*(major_s0_1) + (1158246993923/62500000000 : ℝ)*(major_s0_2) + (762156647/500000000000 : ℝ)*(sp_s0_0) + (1406695621/1000000000000 : ℝ)*(sp_s0_9) + (13729915425367/500000000000 : ℝ)*(sp_s0_14) + (13730654447809/500000000000 : ℝ)*(sp_s0_15) + (27459948468407/1000000000000 : ℝ)*(sp_s0_16) + (1920509031843/200000000000 : ℝ)*(sp_s0_19) + (4626841/100000000000 : ℝ)*(sp_s0_21) + (1920509031843/200000000000 : ℝ)*(f.failure) + (6865338791007/250000000000 : ℝ)*(f.sum) + (62728008358443/156250000000000000000000000 : ℝ)*base62 + (2399057626879/125000000000000000000000000 : ℝ)*base64 + (41454668423121/125000000000000000000000000 : ℝ)*base67 + (55885728437267/78125000000000000000000000 : ℝ)*base68 + (82218118195031/625000000000000000000000000 : ℝ)*base70 + (48018429676879/125000000000000000000000000 : ℝ)*base72 + (28231051710821/39062500000000000000000000 : ℝ)*base74 + (102034829828591/156250000000000000000000000 : ℝ)*base77 + (51400026270629/62500000000000000000000000 : ℝ)*base78 + (2057/2000000000000000 : ℝ)*base87 + (2057/2000000000000000 : ℝ)*base89 + (2057/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5977/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5977/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26492926980133730453697/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9440278576151/1000000000000 : ℝ)*(base39) + (4029133896411/1000000000000 : ℝ)*(base40) + (95522368209/1000000000000 : ℝ)*(base49) + (59799453649/500000000000 : ℝ)*(base59) + (9265932440371/500000000000 : ℝ)*(major_s0_0) + (9265932440371/500000000000 : ℝ)*(major_s0_1) + (9265932440371/500000000000 : ℝ)*(major_s0_2) + (267105369/200000000000 : ℝ)*(sp_s0_7) + (614985953/500000000000 : ℝ)*(sp_s0_8) + (52575207/1000000000000 : ℝ)*(sp_s0_16) + (13729945317247/500000000000 : ℝ)*(sp_s0_20) + (13729998094717/500000000000 : ℝ)*(sp_s0_21) + (6865293396533/250000000000 : ℝ)*(sp_s0_22) + (1920500013549/200000000000 : ℝ)*(sp_s0_25) + (1920500013549/200000000000 : ℝ)*(f.failure) + (27461226161339/1000000000000 : ℝ)*(f.sum) + (222650513076357/625000000000000000000000000 : ℝ)*base63 + (697866253488083/1000000000000000000000000000 : ℝ)*base64 + (738267312988083/1000000000000000000000000000 : ℝ)*base66 + (225760452451357/1250000000000000000000000000 : ℝ)*base69 + (903124996134987/5000000000000000000000000000 : ℝ)*base70 + (419931273588083/1000000000000000000000000000 : ℝ)*base72 + (849580159701357/1250000000000000000000000000 : ℝ)*base75 + (129563504201357/1250000000000000000000000000 : ℝ)*base77 + (378314107988083/500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1849/2000000000000000 : ℝ)*base86 + (1849/2000000000000000 : ℝ)*base88 + (1849/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (439/100000 : ℝ) ^ (41/8 : ℝ) ≤ (82723837/100000000000000000000 : ℝ) := by
    have hpowers : (439/100000 : ℝ)^41 ≤ (82723837/100000000000000000000 : ℝ)^8 := by
      have hnat : (439 : ℕ)^41*100000000000000000000^8 ≤ 82723837^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 100000 82723837 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/100000 : ℝ)) (X := (82723837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100000000000082723837/100000000000000000000 : ℝ) ≤ (2000000000000323/2000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100000000000082723837/100000000000000000000 : ℝ)^8 ≤ (2000000000000323/2000000000000000 : ℝ)^41 := by
      have hnat : (100000000000082723837 : ℕ)^8*2000000000000000^41 ≤ 2000000000000323^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000000000082723837 100000000000000000000 2000000000000323 2000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000000323/2000000000000000 : ℝ)) (X := (100000000000082723837/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50000000000082723837/50000000000000000000 : ℝ) ≤ (10000000000003229/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50000000000082723837/50000000000000000000 : ℝ)^8 ≤ (10000000000003229/10000000000000000 : ℝ)^41 := by
      have hnat : (50000000000082723837 : ℕ)^8*10000000000000000^41 ≤ 10000000000003229^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000082723837 50000000000000000000 10000000000003229 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000003229/10000000000000000 : ℝ)) (X := (50000000000082723837/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(323/8780000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(807/21950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (439/100000 : ℝ)) (alpha := (323/8780000000000 : ℝ)) (beta := (807/21950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (439/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(323/8780000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(807/21950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5977/25000 : ℝ) ^ (41/8 : ℝ) ≤ (65318189998686341/100000000000000000000 : ℝ) := by
    have hpowers : (5977/25000 : ℝ)^41 ≤ (65318189998686341/100000000000000000000 : ℝ)^8 := by
      have hnat : (5977 : ℕ)^41*100000000000000000000^8 ≤ 65318189998686341^8*25000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5977 25000 65318189998686341 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5977/25000 : ℝ)) (X := (65318189998686341/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100065318189998686341/100000000000000000000 : ℝ) ≤ (2500318541594239/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100065318189998686341/100000000000000000000 : ℝ)^8 ≤ (2500318541594239/2500000000000000 : ℝ)^41 := by
      have hnat : (100065318189998686341 : ℕ)^8*2500000000000000^41 ≤ 2500318541594239^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100065318189998686341 100000000000000000000 2500318541594239 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500318541594239/2500000000000000 : ℝ)) (X := (100065318189998686341/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50065318189998686341/50000000000000000000 : ℝ) ≤ (5001273831748591/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50065318189998686341/50000000000000000000 : ℝ)^8 ≤ (5001273831748591/5000000000000000 : ℝ)^41 := by
      have hnat : (50065318189998686341 : ℕ)^8*5000000000000000^41 ≤ 5001273831748591^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50065318189998686341 50000000000000000000 5001273831748591 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001273831748591/5000000000000000 : ℝ)) (X := (50065318189998686341/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(318541594239/597700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(636748560113/1195400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (5977/25000 : ℝ)) (alpha := (318541594239/597700000000000 : ℝ)) (beta := (636748560113/1195400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (5977/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(318541594239/597700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(636748560113/1195400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5977/25000 : ℝ) ^ (41/8 : ℝ) ≤ (65318189998686341/100000000000000000000 : ℝ) := by
    have hpowers : (5977/25000 : ℝ)^41 ≤ (65318189998686341/100000000000000000000 : ℝ)^8 := by
      have hnat : (5977 : ℕ)^41*100000000000000000000^8 ≤ 65318189998686341^8*25000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5977 25000 65318189998686341 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5977/25000 : ℝ)) (X := (65318189998686341/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100065318189998686341/100000000000000000000 : ℝ) ≤ (2500318541594239/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100065318189998686341/100000000000000000000 : ℝ)^8 ≤ (2500318541594239/2500000000000000 : ℝ)^41 := by
      have hnat : (100065318189998686341 : ℕ)^8*2500000000000000^41 ≤ 2500318541594239^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100065318189998686341 100000000000000000000 2500318541594239 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500318541594239/2500000000000000 : ℝ)) (X := (100065318189998686341/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50065318189998686341/50000000000000000000 : ℝ) ≤ (5001273831748591/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50065318189998686341/50000000000000000000 : ℝ)^8 ≤ (5001273831748591/5000000000000000 : ℝ)^41 := by
      have hnat : (50065318189998686341 : ℕ)^8*5000000000000000^41 ≤ 5001273831748591^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50065318189998686341 50000000000000000000 5001273831748591 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001273831748591/5000000000000000 : ℝ)) (X := (50065318189998686341/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(318541594239/597700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(636748560113/1195400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (5977/25000 : ℝ)) (alpha := (318541594239/597700000000000 : ℝ)) (beta := (636748560113/1195400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (5977/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(318541594239/597700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(636748560113/1195400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-72937061/312500000 : ℝ)*X 0 0+(-153975849/312500000 : ℝ)*X 0 1+(-153975849/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((112844143/250000000 : ℝ)*X 1 0+(390342661/1000000000 : ℝ)*X 1 1+(-390342661/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4513765719/10000000000 : ℝ)*X 2 0+(-3903426611/10000000000 : ℝ)*X 2 1+(3903426611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1648732953/2500000000 : ℝ)*X 0 0+(-545740627/2000000000 : ℝ)*X 0 1+(-545740627/2000000000 : ℝ)*X 0 2+(1648732953/2500000000 : ℝ)*X 1 0+(-545740627/2000000000 : ℝ)*X 1 1+(-545740627/2000000000 : ℝ)*X 1 2+(1648732953/2500000000 : ℝ)*X 2 0+(-545740627/2000000000 : ℝ)*X 2 1+(-545740627/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322046_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-221729924017150051848367071483/26239030000000000000000000000 : ℝ) := by norm_num
    linear_combination (18659/1000000000000 : ℝ)*(base8) + (44601147119/40000000000 : ℝ)*(base39) + (557514338847/1000000000000 : ℝ)*(base40) + (268102729721/1000000000000 : ℝ)*(base49) + (13101/500000000000 : ℝ)*(base50) + (134051365001/500000000000 : ℝ)*(base59) + (26483/1000000000000 : ℝ)*(base60) + (19299/10000 : ℝ)*(major_s1_0) + (19299/10000 : ℝ)*(major_s1_1) + (19299/10000 : ℝ)*(major_s1_2) + (704198803989/250000000000 : ℝ)*(sp_s1_0) + (563359046923/200000000000 : ℝ)*(sp_s1_1) + (563359046923/200000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (563359046923/200000000000 : ℝ)*(f.sum) + (9670430317/466953125000000000000000 : ℝ)*base62 + (8646970031/933906250000000000000000 : ℝ)*base64 + (8646970031/933906250000000000000000 : ℝ)*base66 + (170436278253/298850000000000000000000 : ℝ)*base68 + (37346935765191991/524780600000000000000000000 : ℝ)*base71 + (6206749643217/87800000000000000000000 : ℝ)*base73 + (1305572328651/11954000000000000000000000 : ℝ)*base75 + (62702716031367/878000000000000000000000 : ℝ)*base77 + (369672650107519441/5247806000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p022_b025 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 47)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=46 := by omega
  rcases hc with rfl
  · exact collision_c322046 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 47)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_b025 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
