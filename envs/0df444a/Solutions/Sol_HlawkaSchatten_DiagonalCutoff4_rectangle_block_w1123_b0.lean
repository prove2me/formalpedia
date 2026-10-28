-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1123_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:10:21.328996+00:00
-- url     : https://prove2.me/submissions/1cec1e20-8f14-4812-8847-9ca790136fa4

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1123_s0_0 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-948919423/5000000000 : ℝ)*x 0 + (6058732073/10000000000 : ℝ)*x 1 + (119451613/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (948919423/5000000000 : ℝ)^2079 ≤ (2756630279431/25000000000000 : ℝ)^1567 := by
    have hnat : (948919423 : ℕ)^2079*25000000000000^1567 ≤ 2756630279431^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948919423 5000000000 2756630279431 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6058732073/10000000000 : ℝ)^2079 ≤ (51437207080093/100000000000000 : ℝ)^1567 := by
    have hnat : (6058732073 : ℕ)^2079*100000000000000^1567 ≤ 51437207080093^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6058732073 10000000000 51437207080093 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119451613/250000000 : ℝ)^2079 ≤ (4692033973331/12500000000000 : ℝ)^1567 := by
    have hnat : (119451613 : ℕ)^2079*12500000000000^1567 ≤ 4692033973331^1567*250000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119451613 250000000 4692033973331 12500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-948919423/5000000000 : ℝ), (6058732073/10000000000 : ℝ), (119451613/250000000 : ℝ)] ![(2756630279431/25000000000000 : ℝ), (51437207080093/100000000000000 : ℝ), (4692033973331/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-948919423/5000000000 : ℝ)|^2079 ≤ (2756630279431/25000000000000 : ℝ)^1567
        have hw : |(-948919423/5000000000 : ℝ)|=(948919423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6058732073/10000000000 : ℝ)|^2079 ≤ (51437207080093/100000000000000 : ℝ)^1567
        have hw : |(6058732073/10000000000 : ℝ)|=(6058732073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119451613/250000000 : ℝ)|^2079 ≤ (4692033973331/12500000000000 : ℝ)^1567
        have hw : |(119451613/250000000 : ℝ)|=(119451613/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s0_1 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5517863949/10000000000 : ℝ)*x 0 + (-2633338331/10000000000 : ℝ)*x 1 + (2389032313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517863949/10000000000 : ℝ)^2079 ≤ (45435729061989/100000000000000 : ℝ)^1567 := by
    have hnat : (5517863949 : ℕ)^2079*100000000000000^1567 ≤ 45435729061989^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517863949 10000000000 45435729061989 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633338331/10000000000 : ℝ)^2079 ≤ (17027998037183/100000000000000 : ℝ)^1567 := by
    have hnat : (2633338331 : ℕ)^2079*100000000000000^1567 ≤ 17027998037183^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633338331 10000000000 17027998037183 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2389032313/5000000000 : ℝ)^2079 ≤ (18768136445733/50000000000000 : ℝ)^1567 := by
    have hnat : (2389032313 : ℕ)^2079*50000000000000^1567 ≤ 18768136445733^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2389032313 5000000000 18768136445733 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517863949/10000000000 : ℝ), (-2633338331/10000000000 : ℝ), (2389032313/5000000000 : ℝ)] ![(45435729061989/100000000000000 : ℝ), (17027998037183/100000000000000 : ℝ), (18768136445733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517863949/10000000000 : ℝ)|^2079 ≤ (45435729061989/100000000000000 : ℝ)^1567
        have hw : |(5517863949/10000000000 : ℝ)|=(5517863949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2633338331/10000000000 : ℝ)|^2079 ≤ (17027998037183/100000000000000 : ℝ)^1567
        have hw : |(-2633338331/10000000000 : ℝ)|=(2633338331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2389032313/5000000000 : ℝ)|^2079 ≤ (18768136445733/50000000000000 : ℝ)^1567
        have hw : |(2389032313/5000000000 : ℝ)|=(2389032313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s0_2 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5517863817/10000000000 : ℝ)*x 0 + (4778064679/10000000000 : ℝ)*x 1 + (-1316669217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517863817/10000000000 : ℝ)^2079 ≤ (567946595249/1250000000000 : ℝ)^1567 := by
    have hnat : (5517863817 : ℕ)^2079*1250000000000^1567 ≤ 567946595249^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517863817 10000000000 567946595249 1250000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4778064679/10000000000 : ℝ)^2079 ≤ (18768136721937/50000000000000 : ℝ)^1567 := by
    have hnat : (4778064679 : ℕ)^2079*50000000000000^1567 ≤ 18768136721937^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778064679 10000000000 18768136721937 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316669217/5000000000 : ℝ)^2079 ≤ (133031241569/781250000000 : ℝ)^1567 := by
    have hnat : (1316669217 : ℕ)^2079*781250000000^1567 ≤ 133031241569^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316669217 5000000000 133031241569 781250000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517863817/10000000000 : ℝ), (4778064679/10000000000 : ℝ), (-1316669217/5000000000 : ℝ)] ![(567946595249/1250000000000 : ℝ), (18768136721937/50000000000000 : ℝ), (133031241569/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517863817/10000000000 : ℝ)|^2079 ≤ (567946595249/1250000000000 : ℝ)^1567
        have hw : |(5517863817/10000000000 : ℝ)|=(5517863817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4778064679/10000000000 : ℝ)|^2079 ≤ (18768136721937/50000000000000 : ℝ)^1567
        have hw : |(4778064679/10000000000 : ℝ)|=(4778064679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1316669217/5000000000 : ℝ)|^2079 ≤ (133031241569/781250000000 : ℝ)^1567
        have hw : |(-1316669217/5000000000 : ℝ)|=(1316669217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s0_3 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2101266009/5000000000 : ℝ)*x 0 + (97561719/312500000 : ℝ)*x 1 + (5527674/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101266009/5000000000 : ℝ)^2079 ≤ (7914753861579/25000000000000 : ℝ)^1567 := by
    have hnat : (2101266009 : ℕ)^2079*25000000000000^1567 ≤ 7914753861579^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101266009 5000000000 7914753861579 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97561719/312500000 : ℝ)^2079 ≤ (21342230265497/100000000000000 : ℝ)^1567 := by
    have hnat : (97561719 : ℕ)^2079*100000000000000^1567 ≤ 21342230265497^1567*312500000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97561719 312500000 21342230265497 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5527674/9765625 : ℝ)^2079 ≤ (11749688568223/25000000000000 : ℝ)^1567 := by
    have hnat : (5527674 : ℕ)^2079*25000000000000^1567 ≤ 11749688568223^1567*9765625^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527674 9765625 11749688568223 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101266009/5000000000 : ℝ), (97561719/312500000 : ℝ), (5527674/9765625 : ℝ)] ![(7914753861579/25000000000000 : ℝ), (21342230265497/100000000000000 : ℝ), (11749688568223/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101266009/5000000000 : ℝ)|^2079 ≤ (7914753861579/25000000000000 : ℝ)^1567
        have hw : |(2101266009/5000000000 : ℝ)|=(2101266009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(97561719/312500000 : ℝ)|^2079 ≤ (21342230265497/100000000000000 : ℝ)^1567
        have hw : |(97561719/312500000 : ℝ)|=(97561719/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5527674/9765625 : ℝ)|^2079 ≤ (11749688568223/25000000000000 : ℝ)^1567
        have hw : |(5527674/9765625 : ℝ)|=(5527674/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s0_4 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-9515209/50000000 : ℝ)*x 0 + (4811112083/10000000000 : ℝ)*x 1 + (1204904663/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9515209/50000000 : ℝ)^2079 ≤ (5533322780039/50000000000000 : ℝ)^1567 := by
    have hnat : (9515209 : ℕ)^2079*50000000000000^1567 ≤ 5533322780039^1567*50000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9515209 50000000 5533322780039 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4811112083/10000000000 : ℝ)^2079 ≤ (37881108701997/100000000000000 : ℝ)^1567 := by
    have hnat : (4811112083 : ℕ)^2079*100000000000000^1567 ≤ 37881108701997^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4811112083 10000000000 37881108701997 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1204904663/2000000000 : ℝ)^2079 ≤ (25526122861247/50000000000000 : ℝ)^1567 := by
    have hnat : (1204904663 : ℕ)^2079*50000000000000^1567 ≤ 25526122861247^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204904663 2000000000 25526122861247 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9515209/50000000 : ℝ), (4811112083/10000000000 : ℝ), (1204904663/2000000000 : ℝ)] ![(5533322780039/50000000000000 : ℝ), (37881108701997/100000000000000 : ℝ), (25526122861247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9515209/50000000 : ℝ)|^2079 ≤ (5533322780039/50000000000000 : ℝ)^1567
        have hw : |(-9515209/50000000 : ℝ)|=(9515209/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4811112083/10000000000 : ℝ)|^2079 ≤ (37881108701997/100000000000000 : ℝ)^1567
        have hw : |(4811112083/10000000000 : ℝ)|=(4811112083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1204904663/2000000000 : ℝ)|^2079 ≤ (25526122861247/50000000000000 : ℝ)^1567
        have hw : |(1204904663/2000000000 : ℝ)|=(1204904663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s0_5 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (16156153/31250000 : ℝ)*x 0 + (-1386880519/10000000000 : ℝ)*x 1 + (6024527109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16156153/31250000 : ℝ)^2079 ≤ (5209346981113/12500000000000 : ℝ)^1567 := by
    have hnat : (16156153 : ℕ)^2079*12500000000000^1567 ≤ 5209346981113^1567*31250000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16156153 31250000 5209346981113 12500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1386880519/10000000000 : ℝ)^2079 ≤ (181823393923/2500000000000 : ℝ)^1567 := by
    have hnat : (1386880519 : ℕ)^2079*2500000000000^1567 ≤ 181823393923^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386880519 10000000000 181823393923 2500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6024527109/10000000000 : ℝ)^2079 ≤ (6381536047249/12500000000000 : ℝ)^1567 := by
    have hnat : (6024527109 : ℕ)^2079*12500000000000^1567 ≤ 6381536047249^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6024527109 10000000000 6381536047249 12500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16156153/31250000 : ℝ), (-1386880519/10000000000 : ℝ), (6024527109/10000000000 : ℝ)] ![(5209346981113/12500000000000 : ℝ), (181823393923/2500000000000 : ℝ), (6381536047249/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16156153/31250000 : ℝ)|^2079 ≤ (5209346981113/12500000000000 : ℝ)^1567
        have hw : |(16156153/31250000 : ℝ)|=(16156153/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1386880519/10000000000 : ℝ)|^2079 ≤ (181823393923/2500000000000 : ℝ)^1567
        have hw : |(-1386880519/10000000000 : ℝ)|=(1386880519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6024527109/10000000000 : ℝ)|^2079 ≤ (6381536047249/12500000000000 : ℝ)^1567
        have hw : |(6024527109/10000000000 : ℝ)|=(6024527109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s0_6 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5169973797/10000000000 : ℝ)*x 0 + (753065451/1250000000 : ℝ)*x 1 + (-69343937/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169973797/10000000000 : ℝ)^2079 ≤ (520935344743/1250000000000 : ℝ)^1567 := by
    have hnat : (5169973797 : ℕ)^2079*1250000000000^1567 ≤ 520935344743^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169973797 10000000000 520935344743 1250000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (753065451/1250000000 : ℝ)^2079 ≤ (25526124508329/50000000000000 : ℝ)^1567 := by
    have hnat : (753065451 : ℕ)^2079*50000000000000^1567 ≤ 25526124508329^1567*1250000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753065451 1250000000 25526124508329 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69343937/500000000 : ℝ)^2079 ≤ (1454584675889/20000000000000 : ℝ)^1567 := by
    have hnat : (69343937 : ℕ)^2079*20000000000000^1567 ≤ 1454584675889^1567*500000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69343937 500000000 1454584675889 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169973797/10000000000 : ℝ), (753065451/1250000000 : ℝ), (-69343937/500000000 : ℝ)] ![(520935344743/1250000000000 : ℝ), (25526124508329/50000000000000 : ℝ), (1454584675889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169973797/10000000000 : ℝ)|^2079 ≤ (520935344743/1250000000000 : ℝ)^1567
        have hw : |(5169973797/10000000000 : ℝ)|=(5169973797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(753065451/1250000000 : ℝ)|^2079 ≤ (25526124508329/50000000000000 : ℝ)^1567
        have hw : |(753065451/1250000000 : ℝ)|=(753065451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69343937/500000000 : ℝ)|^2079 ≤ (1454584675889/20000000000000 : ℝ)^1567
        have hw : |(-69343937/500000000 : ℝ)|=(69343937/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s0_7 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2106420543/5000000000 : ℝ)*x 0 + (2797420087/5000000000 : ℝ)*x 1 + (1594886891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106420543/5000000000 : ℝ)^2079 ≤ (198513082857/625000000000 : ℝ)^1567 := by
    have hnat : (2106420543 : ℕ)^2079*625000000000^1567 ≤ 198513082857^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106420543 5000000000 198513082857 625000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2797420087/5000000000 : ℝ)^2079 ≤ (1851143465919/4000000000000 : ℝ)^1567 := by
    have hnat : (2797420087 : ℕ)^2079*4000000000000^1567 ≤ 1851143465919^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2797420087 5000000000 1851143465919 4000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594886891/5000000000 : ℝ)^2079 ≤ (21959320075861/100000000000000 : ℝ)^1567 := by
    have hnat : (1594886891 : ℕ)^2079*100000000000000^1567 ≤ 21959320075861^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594886891 5000000000 21959320075861 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2106420543/5000000000 : ℝ), (2797420087/5000000000 : ℝ), (1594886891/5000000000 : ℝ)] ![(198513082857/625000000000 : ℝ), (1851143465919/4000000000000 : ℝ), (21959320075861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2106420543/5000000000 : ℝ)|^2079 ≤ (198513082857/625000000000 : ℝ)^1567
        have hw : |(2106420543/5000000000 : ℝ)|=(2106420543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2797420087/5000000000 : ℝ)|^2079 ≤ (1851143465919/4000000000000 : ℝ)^1567
        have hw : |(2797420087/5000000000 : ℝ)|=(2797420087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1594886891/5000000000 : ℝ)|^2079 ≤ (21959320075861/100000000000000 : ℝ)^1567
        have hw : |(1594886891/5000000000 : ℝ)|=(1594886891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1123_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (67/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1743/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (0 : ℝ) ^ (8315/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8315 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8315*1^2048 ≤ 0^2048*1^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8315/2048 : ℝ) ≤ (151432909065286659/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8315 ≤ (151432909065286659/6250000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8315*6250000000000000000^2048 ≤ 151432909065286659^2048*5^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 151432909065286659 6250000000000000000 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (151432909065286659/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8315 := by
      have hnat : (1 : ℕ)^2048*1^8315 ≤ 1^8315*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6401432909065286659/6250000000000000000 : ℝ) ≤ (10059139825221277/10000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (6401432909065286659/6250000000000000000 : ℝ)^2048 ≤ (10059139825221277/10000000000000000 : ℝ)^8315 := by
      have hnat : (6401432909065286659 : ℕ)^2048*10000000000000000^8315 ≤ 10059139825221277^8315*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6401432909065286659 6250000000000000000 10059139825221277 10000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059139825221277/10000000000000000 : ℝ)) (X := (6401432909065286659/6250000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3276432909065286659/3125000000000000000 : ℝ) ≤ (5059139825221277/5000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (3276432909065286659/3125000000000000000 : ℝ)^2048 ≤ (5059139825221277/5000000000000000 : ℝ)^8315 := by
      have hnat : (3276432909065286659 : ℕ)^2048*5000000000000000^8315 ≤ 5059139825221277^8315*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3276432909065286659 3125000000000000000 5059139825221277 5000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059139825221277/5000000000000000 : ℝ)) (X := (3276432909065286659/3125000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59139825221277/4000000000000000 : ℝ)*(0 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(59139825221277/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(151432909065286659/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59139825221277/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8315/2048 : ℝ) := by
    rw [show (1 : ℝ)+(59139825221277/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059139825221277/10000000000000000 : ℝ) by norm_num, show 1+(151432909065286659/6250000000000000000 : ℝ)+(0 : ℝ)=(6401432909065286659/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(151432909065286659/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59139825221277/4000000000000000 : ℝ)*(2/5 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(59139825221277/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059139825221277/5000000000000000 : ℝ) by norm_num, show 1+2*(151432909065286659/6250000000000000000 : ℝ)=(3276432909065286659/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59139825221277/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59139825221277/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59139825221277/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59139825221277/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59139825221277/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59139825221277/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-948919423/5000000000 : ℝ)*X 0 0+(6058732073/10000000000 : ℝ)*X 0 1+(119451613/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5517863949/10000000000 : ℝ)*X 1 0+(-2633338331/10000000000 : ℝ)*X 1 1+(2389032313/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5517863817/10000000000 : ℝ)*X 2 0+(4778064679/10000000000 : ℝ)*X 2 1+(-1316669217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2101266009/5000000000 : ℝ)*X 0 0+(97561719/312500000 : ℝ)*X 0 1+(5527674/9765625 : ℝ)*X 0 2+(2101266009/5000000000 : ℝ)*X 1 0+(97561719/312500000 : ℝ)*X 1 1+(5527674/9765625 : ℝ)*X 1 2+(2101266009/5000000000 : ℝ)*X 2 0+(97561719/312500000 : ℝ)*X 2 1+(5527674/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-9515209/50000000 : ℝ)*X 0 0+(4811112083/10000000000 : ℝ)*X 0 1+(1204904663/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((16156153/31250000 : ℝ)*X 1 0+(-1386880519/10000000000 : ℝ)*X 1 1+(6024527109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5169973797/10000000000 : ℝ)*X 2 0+(753065451/1250000000 : ℝ)*X 2 1+(-69343937/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2106420543/5000000000 : ℝ)*X 0 0+(2797420087/5000000000 : ℝ)*X 0 1+(1594886891/5000000000 : ℝ)*X 0 2+(2106420543/5000000000 : ℝ)*X 1 0+(2797420087/5000000000 : ℝ)*X 1 1+(1594886891/5000000000 : ℝ)*X 1 2+(2106420543/5000000000 : ℝ)*X 2 0+(2797420087/5000000000 : ℝ)*X 2 1+(1594886891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (457116171282825320385441/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23325179/50000000000000 : ℝ)*(base1) + (586733373/50000000000000 : ℝ)*(base19) + (216343037/20000000000000 : ℝ)*(base23) + (18267969/25000000000000 : ℝ)*(base24) + (13726783/5000000000000 : ℝ)*(upper3) + (587403749028563/100000000000000 : ℝ)*(major0) + (587403749028563/100000000000000 : ℝ)*(major1) + (587403749028563/100000000000000 : ℝ)*(major2) + (78084676421723/10000000000000 : ℝ)*(sp0) + (780848145295231/100000000000000 : ℝ)*(sp1) + (195212040993729/25000000000000 : ℝ)*(sp2) + (393955894294887/100000000000000 : ℝ)*(sp3) + (520239021/20000000000000 : ℝ)*(sp4) + (26074723/1250000000000 : ℝ)*(sp7) + (78791605384617/20000000000000 : ℝ)*(f.failure) + (780849318761977/100000000000000 : ℝ)*(f.sum) + (406831143134951/200000000000000000000000000000 : ℝ)*base65 + (735955363934951/400000000000000000000000000000 : ℝ)*base67 + (3065295401534951/400000000000000000000000000000 : ℝ)*base69 + (2441093898334951/400000000000000000000000000000 : ℝ)*base71 + (235569509334951/200000000000000000000000000000 : ℝ)*base73 + (2107077029134951/400000000000000000000000000000 : ℝ)*base75 + (1322899037134951/400000000000000000000000000000 : ℝ)*base77 + (2201787180334951/400000000000000000000000000000 : ℝ)*base79 + (1507600178734951/200000000000000000000000000000 : ℝ)*base81 + (1144879/200000000000000000000 : ℝ)*base90 + (1144879/200000000000000000000 : ℝ)*base92 + (1144879/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6585089668675987143021/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (79658977/50000000000000 : ℝ)*(base13) + (158121191/12500000000000 : ℝ)*(base23) + (110098631/25000000000000 : ℝ)*(base39) + (158133993/100000000000000 : ℝ)*(upper3) + (239394349/100000000000000 : ℝ)*(upper5) + (15498865862751/2500000000000 : ℝ)*(major0) + (15498865862751/2500000000000 : ℝ)*(major1) + (154988548528879/25000000000000 : ℝ)*(major2) + (9145931/1250000000000 : ℝ)*(sp1) + (857200473/50000000000000 : ℝ)*(sp2) + (164823876079061/20000000000000 : ℝ)*(sp4) + (824118808038779/100000000000000 : ℝ)*(sp5) + (206029250184327/25000000000000 : ℝ)*(sp6) + (207894574215189/50000000000000 : ℝ)*(sp7) + (207894574215189/50000000000000 : ℝ)*(f.failure) + (412059990053891/50000000000000 : ℝ)*(f.sum) + (128543718488753/100000000000000000000000000000 : ℝ)*base65 + (204721391058483/100000000000000000000000000000 : ℝ)*base67 + (19842230243027/10000000000000000000000000000 : ℝ)*base69 + (277505812958483/100000000000000000000000000000 : ℝ)*base71 + (350933210188753/100000000000000000000000000000 : ℝ)*base73 + (9704452916973/10000000000000000000000000000 : ℝ)*base76 + (24168088293027/10000000000000000000000000000 : ℝ)*base77 + (40144493253027/10000000000000000000000000000 : ℝ)*base79 + (25605291393027/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2655843/500000000000000000000 : ℝ)*base90 + (2655843/500000000000000000000 : ℝ)*base92 + (2655843/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1123_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (67/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1743/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1123_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1123_s1_0 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2103876439/10000000000 : ℝ)*x 0 + (713326907/1250000000 : ℝ)*x 1 + (4998268153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103876439/10000000000 : ℝ)^2079 ≤ (158028186267/1250000000000 : ℝ)^1567 := by
    have hnat : (2103876439 : ℕ)^2079*1250000000000^1567 ≤ 158028186267^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103876439 10000000000 158028186267 1250000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (713326907/1250000000 : ℝ)^2079 ≤ (4750922874711/10000000000000 : ℝ)^1567 := by
    have hnat : (713326907 : ℕ)^2079*10000000000000^1567 ≤ 4750922874711^1567*1250000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713326907 1250000000 4750922874711 10000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4998268153/10000000000 : ℝ)^2079 ≤ (39848516329267/100000000000000 : ℝ)^1567 := by
    have hnat : (4998268153 : ℕ)^2079*100000000000000^1567 ≤ 39848516329267^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998268153 10000000000 39848516329267 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2103876439/10000000000 : ℝ), (713326907/1250000000 : ℝ), (4998268153/10000000000 : ℝ)] ![(158028186267/1250000000000 : ℝ), (4750922874711/10000000000000 : ℝ), (39848516329267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2103876439/10000000000 : ℝ)|^2079 ≤ (158028186267/1250000000000 : ℝ)^1567
        have hw : |(-2103876439/10000000000 : ℝ)|=(2103876439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(713326907/1250000000 : ℝ)|^2079 ≤ (4750922874711/10000000000000 : ℝ)^1567
        have hw : |(713326907/1250000000 : ℝ)|=(713326907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4998268153/10000000000 : ℝ)|^2079 ≤ (39848516329267/100000000000000 : ℝ)^1567
        have hw : |(4998268153/10000000000 : ℝ)|=(4998268153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s1_1 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5420166737/10000000000 : ℝ)*x 0 + (-2486511697/10000000000 : ℝ)*x 1 + (4998267877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420166737/10000000000 : ℝ)^2079 ≤ (11092877465361/25000000000000 : ℝ)^1567 := by
    have hnat : (5420166737 : ℕ)^2079*25000000000000^1567 ≤ 11092877465361^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420166737 10000000000 11092877465361 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2486511697/10000000000 : ℝ)^2079 ≤ (7889988359079/50000000000000 : ℝ)^1567 := by
    have hnat : (2486511697 : ℕ)^2079*50000000000000^1567 ≤ 7889988359079^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486511697 10000000000 7889988359079 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4998267877/10000000000 : ℝ)^2079 ≤ (39848513409911/100000000000000 : ℝ)^1567 := by
    have hnat : (4998267877 : ℕ)^2079*100000000000000^1567 ≤ 39848513409911^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998267877 10000000000 39848513409911 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420166737/10000000000 : ℝ), (-2486511697/10000000000 : ℝ), (4998267877/10000000000 : ℝ)] ![(11092877465361/25000000000000 : ℝ), (7889988359079/50000000000000 : ℝ), (39848513409911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420166737/10000000000 : ℝ)|^2079 ≤ (11092877465361/25000000000000 : ℝ)^1567
        have hw : |(5420166737/10000000000 : ℝ)|=(5420166737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2486511697/10000000000 : ℝ)|^2079 ≤ (7889988359079/50000000000000 : ℝ)^1567
        have hw : |(-2486511697/10000000000 : ℝ)|=(2486511697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4998267877/10000000000 : ℝ)|^2079 ≤ (39848513409911/100000000000000 : ℝ)^1567
        have hw : |(4998267877/10000000000 : ℝ)|=(4998267877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s1_2 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1355042077/2500000000 : ℝ)*x 0 + (4998266443/10000000000 : ℝ)*x 1 + (-155406967/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355042077/2500000000 : ℝ)^2079 ≤ (1109288173109/2500000000000 : ℝ)^1567 := by
    have hnat : (1355042077 : ℕ)^2079*2500000000000^1567 ≤ 1109288173109^1567*2500000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355042077 2500000000 1109288173109 2500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4998266443/10000000000 : ℝ)^2079 ≤ (39848498241949/100000000000000 : ℝ)^1567 := by
    have hnat : (4998266443 : ℕ)^2079*100000000000000^1567 ≤ 39848498241949^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998266443 10000000000 39848498241949 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (155406967/625000000 : ℝ)^2079 ≤ (3155994964741/20000000000000 : ℝ)^1567 := by
    have hnat : (155406967 : ℕ)^2079*20000000000000^1567 ≤ 3155994964741^1567*625000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155406967 625000000 3155994964741 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355042077/2500000000 : ℝ), (4998266443/10000000000 : ℝ), (-155406967/625000000 : ℝ)] ![(1109288173109/2500000000000 : ℝ), (39848498241949/100000000000000 : ℝ), (3155994964741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355042077/2500000000 : ℝ)|^2079 ≤ (1109288173109/2500000000000 : ℝ)^1567
        have hw : |(1355042077/2500000000 : ℝ)|=(1355042077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4998266443/10000000000 : ℝ)|^2079 ≤ (39848498241949/100000000000000 : ℝ)^1567
        have hw : |(4998266443/10000000000 : ℝ)|=(4998266443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-155406967/625000000 : ℝ)|^2079 ≤ (3155994964741/20000000000000 : ℝ)^1567
        have hw : |(-155406967/625000000 : ℝ)|=(155406967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s1_3 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (539880443/1250000000 : ℝ)*x 0 + (1836729657/5000000000 : ℝ)*x 1 + (5077445757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539880443/1250000000 : ℝ)^2079 ≤ (6565752150559/20000000000000 : ℝ)^1567 := by
    have hnat : (539880443 : ℕ)^2079*20000000000000^1567 ≤ 6565752150559^1567*1250000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539880443 1250000000 6565752150559 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1836729657/5000000000 : ℝ)^2079 ≤ (1324153579813/5000000000000 : ℝ)^1567 := by
    have hnat : (1836729657 : ℕ)^2079*5000000000000^1567 ≤ 1324153579813^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836729657 5000000000 1324153579813 5000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5077445757/10000000000 : ℝ)^2079 ≤ (20344083818133/50000000000000 : ℝ)^1567 := by
    have hnat : (5077445757 : ℕ)^2079*50000000000000^1567 ≤ 20344083818133^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077445757 10000000000 20344083818133 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539880443/1250000000 : ℝ), (1836729657/5000000000 : ℝ), (5077445757/10000000000 : ℝ)] ![(6565752150559/20000000000000 : ℝ), (1324153579813/5000000000000 : ℝ), (20344083818133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539880443/1250000000 : ℝ)|^2079 ≤ (6565752150559/20000000000000 : ℝ)^1567
        have hw : |(539880443/1250000000 : ℝ)|=(539880443/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1836729657/5000000000 : ℝ)|^2079 ≤ (1324153579813/5000000000000 : ℝ)^1567
        have hw : |(1836729657/5000000000 : ℝ)|=(1836729657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5077445757/10000000000 : ℝ)|^2079 ≤ (20344083818133/50000000000000 : ℝ)^1567
        have hw : |(5077445757/10000000000 : ℝ)|=(5077445757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s1_4 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-420941909/2000000000 : ℝ)*x 0 + (500801039/1000000000 : ℝ)*x 1 + (5696678741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420941909/2000000000 : ℝ)^2079 ≤ (12648897196359/100000000000000 : ℝ)^1567 := by
    have hnat : (420941909 : ℕ)^2079*100000000000000^1567 ≤ 12648897196359^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420941909 2000000000 12648897196359 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500801039/1000000000 : ℝ)^2079 ≤ (19975798234209/50000000000000 : ℝ)^1567 := by
    have hnat : (500801039 : ℕ)^2079*50000000000000^1567 ≤ 19975798234209^1567*1000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500801039 1000000000 19975798234209 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5696678741/10000000000 : ℝ)^2079 ≤ (23699753165071/50000000000000 : ℝ)^1567 := by
    have hnat : (5696678741 : ℕ)^2079*50000000000000^1567 ≤ 23699753165071^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5696678741 10000000000 23699753165071 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420941909/2000000000 : ℝ), (500801039/1000000000 : ℝ), (5696678741/10000000000 : ℝ)] ![(12648897196359/100000000000000 : ℝ), (19975798234209/50000000000000 : ℝ), (23699753165071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420941909/2000000000 : ℝ)|^2079 ≤ (12648897196359/100000000000000 : ℝ)^1567
        have hw : |(-420941909/2000000000 : ℝ)|=(420941909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(500801039/1000000000 : ℝ)|^2079 ≤ (19975798234209/50000000000000 : ℝ)^1567
        have hw : |(500801039/1000000000 : ℝ)|=(500801039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5696678741/10000000000 : ℝ)|^2079 ≤ (23699753165071/50000000000000 : ℝ)^1567
        have hw : |(5696678741/10000000000 : ℝ)|=(5696678741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s1_5 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (130968331/250000000 : ℝ)*x 0 + (-1788100457/10000000000 : ℝ)*x 1 + (5696678507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130968331/250000000 : ℝ)^2079 ≤ (2120589311301/5000000000000 : ℝ)^1567 := by
    have hnat : (130968331 : ℕ)^2079*5000000000000^1567 ≤ 2120589311301^1567*250000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130968331 250000000 2120589311301 5000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1788100457/10000000000 : ℝ)^2079 ≤ (10188710020649/100000000000000 : ℝ)^1567 := by
    have hnat : (1788100457 : ℕ)^2079*100000000000000^1567 ≤ 10188710020649^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788100457 10000000000 10188710020649 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5696678507/10000000000 : ℝ)^2079 ≤ (47399503746969/100000000000000 : ℝ)^1567 := by
    have hnat : (5696678507 : ℕ)^2079*100000000000000^1567 ≤ 47399503746969^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5696678507 10000000000 47399503746969 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130968331/250000000 : ℝ), (-1788100457/10000000000 : ℝ), (5696678507/10000000000 : ℝ)] ![(2120589311301/5000000000000 : ℝ), (10188710020649/100000000000000 : ℝ), (47399503746969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130968331/250000000 : ℝ)|^2079 ≤ (2120589311301/5000000000000 : ℝ)^1567
        have hw : |(130968331/250000000 : ℝ)|=(130968331/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1788100457/10000000000 : ℝ)|^2079 ≤ (10188710020649/100000000000000 : ℝ)^1567
        have hw : |(-1788100457/10000000000 : ℝ)|=(1788100457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5696678507/10000000000 : ℝ)|^2079 ≤ (47399503746969/100000000000000 : ℝ)^1567
        have hw : |(5696678507/10000000000 : ℝ)|=(5696678507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s1_6 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5238733277/10000000000 : ℝ)*x 0 + (5696678667/10000000000 : ℝ)*x 1 + (-1788100171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5238733277/10000000000 : ℝ)^2079 ≤ (21205893311719/50000000000000 : ℝ)^1567 := by
    have hnat : (5238733277 : ℕ)^2079*50000000000000^1567 ≤ 21205893311719^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238733277 10000000000 21205893311719 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5696678667/10000000000 : ℝ)^2079 ≤ (47399505513241/100000000000000 : ℝ)^1567 := by
    have hnat : (5696678667 : ℕ)^2079*100000000000000^1567 ≤ 47399505513241^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5696678667 10000000000 47399505513241 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1788100171/10000000000 : ℝ)^2079 ≤ (5094353929267/50000000000000 : ℝ)^1567 := by
    have hnat : (1788100171 : ℕ)^2079*50000000000000^1567 ≤ 5094353929267^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788100171 10000000000 5094353929267 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5238733277/10000000000 : ℝ), (5696678667/10000000000 : ℝ), (-1788100171/10000000000 : ℝ)] ![(21205893311719/50000000000000 : ℝ), (47399505513241/100000000000000 : ℝ), (5094353929267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5238733277/10000000000 : ℝ)|^2079 ≤ (21205893311719/50000000000000 : ℝ)^1567
        have hw : |(5238733277/10000000000 : ℝ)|=(5238733277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5696678667/10000000000 : ℝ)|^2079 ≤ (47399505513241/100000000000000 : ℝ)^1567
        have hw : |(5696678667/10000000000 : ℝ)|=(5696678667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1788100171/10000000000 : ℝ)|^2079 ≤ (5094353929267/50000000000000 : ℝ)^1567
        have hw : |(-1788100171/10000000000 : ℝ)|=(1788100171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s1_7 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4320692379/10000000000 : ℝ)*x 0 + (5058136821/10000000000 : ℝ)*x 1 + (3693153111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320692379/10000000000 : ℝ)^2079 ≤ (1313815575633/4000000000000 : ℝ)^1567 := by
    have hnat : (4320692379 : ℕ)^2079*4000000000000^1567 ≤ 1313815575633^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320692379 10000000000 1313815575633 4000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5058136821/10000000000 : ℝ)^2079 ≤ (20241502907777/50000000000000 : ℝ)^1567 := by
    have hnat : (5058136821 : ℕ)^2079*50000000000000^1567 ≤ 20241502907777^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5058136821 10000000000 20241502907777 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3693153111/10000000000 : ℝ)^2079 ≤ (13335802394133/50000000000000 : ℝ)^1567 := by
    have hnat : (3693153111 : ℕ)^2079*50000000000000^1567 ≤ 13335802394133^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3693153111 10000000000 13335802394133 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320692379/10000000000 : ℝ), (5058136821/10000000000 : ℝ), (3693153111/10000000000 : ℝ)] ![(1313815575633/4000000000000 : ℝ), (20241502907777/50000000000000 : ℝ), (13335802394133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320692379/10000000000 : ℝ)|^2079 ≤ (1313815575633/4000000000000 : ℝ)^1567
        have hw : |(4320692379/10000000000 : ℝ)|=(4320692379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5058136821/10000000000 : ℝ)|^2079 ≤ (20241502907777/50000000000000 : ℝ)^1567
        have hw : |(5058136821/10000000000 : ℝ)|=(5058136821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3693153111/10000000000 : ℝ)|^2079 ≤ (13335802394133/50000000000000 : ℝ)^1567
        have hw : |(3693153111/10000000000 : ℝ)|=(3693153111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1123_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1743/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5543/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5131/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1743/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (67/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1743/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (67/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1743/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (67/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1743/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (67/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1743/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (67/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1743/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (67/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (67/20000 : ℝ) ^ (8315/2048 : ℝ) ≤ (447205261/5000000000000000000 : ℝ) := by
    have hpowers : (67/20000 : ℝ)^8315 ≤ (447205261/5000000000000000000 : ℝ)^2048 := by
      have hnat : (67 : ℕ)^8315*5000000000000000000^2048 ≤ 447205261^2048*20000^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67 20000 447205261 5000000000000000000 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67/20000 : ℝ)) (X := (447205261/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1743/6250 : ℝ) ^ (8315/2048 : ℝ) ≤ (175070127427863/31250000000000000 : ℝ) := by
    have hpowers : (1743/6250 : ℝ)^8315 ≤ (175070127427863/31250000000000000 : ℝ)^2048 := by
      have hnat : (1743 : ℕ)^8315*31250000000000000^2048 ≤ 175070127427863^2048*6250^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1743 6250 175070127427863 31250000000000000 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1743/6250 : ℝ)) (X := (175070127427863/31250000000000000 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500000000447205261/2500000000000000000 : ℝ) ≤ (1000000000044059/1000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (2500000000447205261/2500000000000000000 : ℝ)^2048 ≤ (1000000000044059/1000000000000000 : ℝ)^8315 := by
      have hnat : (2500000000447205261 : ℕ)^2048*1000000000000000^8315 ≤ 1000000000044059^8315*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500000000447205261 2500000000000000000 1000000000044059 1000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000000044059/1000000000000000 : ℝ)) (X := (2500000000447205261/2500000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5028011220835663341/5000000000000000000 : ℝ) ≤ (10013769395594113/10000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (5028011220835663341/5000000000000000000 : ℝ)^2048 ≤ (10013769395594113/10000000000000000 : ℝ)^8315 := by
      have hnat : (5028011220835663341 : ℕ)^2048*10000000000000000^8315 ≤ 10013769395594113^8315*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5028011220835663341 5000000000000000000 10013769395594113 10000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013769395594113/10000000000000000 : ℝ)) (X := (5028011220835663341/5000000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (15800070127427863/15625000000000000 : ℝ) ≤ (2506884697686909/2500000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (15800070127427863/15625000000000000 : ℝ)^2048 ≤ (2506884697686909/2500000000000000 : ℝ)^8315 := by
      have hnat : (15800070127427863 : ℕ)^2048*2500000000000000^8315 ≤ 2506884697686909^8315*15625000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15800070127427863 15625000000000000 2506884697686909 2500000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506884697686909/2500000000000000 : ℝ)) (X := (15800070127427863/15625000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(447205261/5000000000000000000 : ℝ) ≤ ((13776038725869335793/13776500000000000000 : ℝ)+2*(13769395153523/2755300000000000 : ℝ)*(67/20000 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (13776038725869335793/13776500000000000000 : ℝ)+2*(13769395153523/2755300000000000 : ℝ)*(67/20000 : ℝ)=(1000000000044059/1000000000000000 : ℝ) by norm_num, show 1+2*(447205261/5000000000000000000 : ℝ)=(2500000000447205261/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(175070127427863/31250000000000000 : ℝ)+(447205261/5000000000000000000 : ℝ) ≤ ((13776038725869335793/13776500000000000000 : ℝ)+(13769395153523/2755300000000000 : ℝ)*((1743/6250 : ℝ)+(67/20000 : ℝ)))^(8315/2048 : ℝ) := by
    rw [show (13776038725869335793/13776500000000000000 : ℝ)+(13769395153523/2755300000000000 : ℝ)*((1743/6250 : ℝ)+(67/20000 : ℝ))=(10013769395594113/10000000000000000 : ℝ) by norm_num, show 1+(175070127427863/31250000000000000 : ℝ)+(447205261/5000000000000000000 : ℝ)=(5028011220835663341/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(175070127427863/31250000000000000 : ℝ) ≤ ((13776038725869335793/13776500000000000000 : ℝ)+2*(13769395153523/2755300000000000 : ℝ)*(1743/6250 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (13776038725869335793/13776500000000000000 : ℝ)+2*(13769395153523/2755300000000000 : ℝ)*(1743/6250 : ℝ)=(2506884697686909/2500000000000000 : ℝ) by norm_num, show 1+2*(175070127427863/31250000000000000 : ℝ)=(15800070127427863/15625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13776038725869335793/13776500000000000000 : ℝ)*(X 1 0+X 2 0)+(13769395153523/2755300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (67/20000 : ℝ)) (hi := (1743/6250 : ℝ)) (c := (13776038725869335793/13776500000000000000 : ℝ)) (alpha := (13769395153523/2755300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13776038725869335793/13776500000000000000 : ℝ)*(X 0 1+X 2 1)+(13769395153523/2755300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (67/20000 : ℝ)) (hi := (1743/6250 : ℝ)) (c := (13776038725869335793/13776500000000000000 : ℝ)) (alpha := (13769395153523/2755300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13776038725869335793/13776500000000000000 : ℝ)*(X 0 2+X 1 2)+(13769395153523/2755300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (67/20000 : ℝ)) (hi := (1743/6250 : ℝ)) (c := (13776038725869335793/13776500000000000000 : ℝ)) (alpha := (13769395153523/2755300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2103876439/10000000000 : ℝ)*X 0 0+(713326907/1250000000 : ℝ)*X 0 1+(4998268153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420166737/10000000000 : ℝ)*X 1 0+(-2486511697/10000000000 : ℝ)*X 1 1+(4998267877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1355042077/2500000000 : ℝ)*X 2 0+(4998266443/10000000000 : ℝ)*X 2 1+(-155406967/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539880443/1250000000 : ℝ)*X 0 0+(1836729657/5000000000 : ℝ)*X 0 1+(5077445757/10000000000 : ℝ)*X 0 2+(539880443/1250000000 : ℝ)*X 1 0+(1836729657/5000000000 : ℝ)*X 1 1+(5077445757/10000000000 : ℝ)*X 1 2+(539880443/1250000000 : ℝ)*X 2 0+(1836729657/5000000000 : ℝ)*X 2 1+(5077445757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-420941909/2000000000 : ℝ)*X 0 0+(500801039/1000000000 : ℝ)*X 0 1+(5696678741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((130968331/250000000 : ℝ)*X 1 0+(-1788100457/10000000000 : ℝ)*X 1 1+(5696678507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5238733277/10000000000 : ℝ)*X 2 0+(5696678667/10000000000 : ℝ)*X 2 1+(-1788100171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320692379/10000000000 : ℝ)*X 0 0+(5058136821/10000000000 : ℝ)*X 0 1+(3693153111/10000000000 : ℝ)*X 0 2+(4320692379/10000000000 : ℝ)*X 1 0+(5058136821/10000000000 : ℝ)*X 1 1+(3693153111/10000000000 : ℝ)*X 1 2+(4320692379/10000000000 : ℝ)*X 2 0+(5058136821/10000000000 : ℝ)*X 2 1+(3693153111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (230960985563627373223113/137765000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5341369/5000000000000 : ℝ)*(base1) + (202945957/100000000000000 : ℝ)*(base19) + (48370947/10000000000000 : ℝ)*(base23) + (54124751/50000000000000 : ℝ)*(base37) + (3738837/5000000000000 : ℝ)*(lower2) + (265499165951093/25000000000000 : ℝ)*(major0) + (265499165951093/25000000000000 : ℝ)*(major1) + (265499165951093/25000000000000 : ℝ)*(major2) + (352934127589337/25000000000000 : ℝ)*(sp0) + (1411736331581551/100000000000000 : ℝ)*(sp1) + (352934083962957/25000000000000 : ℝ)*(sp2) + (356128118543859/50000000000000 : ℝ)*(sp3) + (416031331/100000000000000 : ℝ)*(sp4) + (28503379/10000000000000 : ℝ)*(sp5) + (712256452164601/100000000000000 : ℝ)*(f.failure) + (705868409780649/50000000000000 : ℝ)*(f.sum) + (228855140157569/137765000000000000000000000000 : ℝ)*base66 + (305679657381808251/344412500000000000000000000000000 : ℝ)*base68 + (1276010011397845751/344412500000000000000000000000000 : ℝ)*base70 + (1662739158281979249/344412500000000000000000000000000 : ℝ)*base71 + (18481672775681/137765000000000000000000000000 : ℝ)*base73 + (41258883404329249/344412500000000000000000000000000 : ℝ)*base75 + (672452789710033251/344412500000000000000000000000000 : ℝ)*base78 + (593038026003466749/344412500000000000000000000000000 : ℝ)*base79 + (120945734037797/68882500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (8430113/1000000000000000000000 : ℝ)*base89 + (8430113/1000000000000000000000 : ℝ)*base91 + (8430113/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (612682545920934296740220367/86103125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85878403/100000000000000 : ℝ)*(base1) + (31641379/2000000000000 : ℝ)*(base19) + (805989127/50000000000000 : ℝ)*(base23) + (77275349/50000000000000 : ℝ)*(upper3) + (159711651/100000000000000 : ℝ)*(upper5) + (34135744051781/3125000000000 : ℝ)*(major0) + (34135744051781/3125000000000 : ℝ)*(major1) + (34135744051781/3125000000000 : ℝ)*(major2) + (1269636019/20000000000000 : ℝ)*(sp1) + (6915602527/100000000000000 : ℝ)*(sp2) + (1452077891224113/100000000000000 : ℝ)*(sp4) + (181508734387083/12500000000000 : ℝ)*(sp5) + (1452069277764929/100000000000000 : ℝ)*(sp6) + (73260949090043/10000000000000 : ℝ)*(sp7) + (45788098548677/6250000000000 : ℝ)*(f.failure) + (145207780534571/10000000000000 : ℝ)*(f.sum) + (308466937116709/137765000000000000000000000000 : ℝ)*base66 + (435189408006331417/43051562500000000000000000000000 : ℝ)*base68 + (126684803068097209/86103125000000000000000000000000 : ℝ)*base70 + (52000233829803459/86103125000000000000000000000000 : ℝ)*base72 + (1045030537966939/137765000000000000000000000000 : ℝ)*base74 + (595563085468809041/86103125000000000000000000000000 : ℝ)*base75 + (395684755500184709/86103125000000000000000000000000 : ℝ)*base78 + (100981733845198521/21525781250000000000000000000000 : ℝ)*base80 + (121351861038339/137765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (194099/62500000000000000000 : ℝ)*base90 + (194099/62500000000000000000 : ℝ)*base92 + (194099/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1123_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1743/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5543/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5131/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1123_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1123_s2_0 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158133683/10000000000 : ℝ)*x 0 + (1378615487/2500000000 : ℝ)*x 1 + (5155939909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158133683/10000000000 : ℝ)^2079 ≤ (6538314045839/50000000000000 : ℝ)^1567 := by
    have hnat : (2158133683 : ℕ)^2079*50000000000000^1567 ≤ 6538314045839^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158133683 10000000000 6538314045839 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378615487/2500000000 : ℝ)^2079 ≤ (5674820844119/12500000000000 : ℝ)^1567 := by
    have hnat : (1378615487 : ℕ)^2079*12500000000000^1567 ≤ 5674820844119^1567*2500000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378615487 2500000000 5674820844119 12500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5155939909/10000000000 : ℝ)^2079 ≤ (41524805143243/100000000000000 : ℝ)^1567 := by
    have hnat : (5155939909 : ℕ)^2079*100000000000000^1567 ≤ 41524805143243^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155939909 10000000000 41524805143243 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158133683/10000000000 : ℝ), (1378615487/2500000000 : ℝ), (5155939909/10000000000 : ℝ)] ![(6538314045839/50000000000000 : ℝ), (5674820844119/12500000000000 : ℝ), (41524805143243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158133683/10000000000 : ℝ)|^2079 ≤ (6538314045839/50000000000000 : ℝ)^1567
        have hw : |(-2158133683/10000000000 : ℝ)|=(2158133683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1378615487/2500000000 : ℝ)|^2079 ≤ (5674820844119/12500000000000 : ℝ)^1567
        have hw : |(1378615487/2500000000 : ℝ)|=(1378615487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5155939909/10000000000 : ℝ)|^2079 ≤ (41524805143243/100000000000000 : ℝ)^1567
        have hw : |(5155939909/10000000000 : ℝ)|=(5155939909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s2_1 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074937113/2000000000 : ℝ)*x 0 + (-234466931/1000000000 : ℝ)*x 1 + (5155941447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074937113/2000000000 : ℝ)^2079 ≤ (21939104534583/50000000000000 : ℝ)^1567 := by
    have hnat : (1074937113 : ℕ)^2079*50000000000000^1567 ≤ 21939104534583^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074937113 2000000000 21939104534583 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234466931/1000000000 : ℝ)^2079 ≤ (1459696933401/10000000000000 : ℝ)^1567 := by
    have hnat : (234466931 : ℕ)^2079*10000000000000^1567 ≤ 1459696933401^1567*1000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234466931 1000000000 1459696933401 10000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5155941447/10000000000 : ℝ)^2079 ≤ (41524821577179/100000000000000 : ℝ)^1567 := by
    have hnat : (5155941447 : ℕ)^2079*100000000000000^1567 ≤ 41524821577179^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155941447 10000000000 41524821577179 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074937113/2000000000 : ℝ), (-234466931/1000000000 : ℝ), (5155941447/10000000000 : ℝ)] ![(21939104534583/50000000000000 : ℝ), (1459696933401/10000000000000 : ℝ), (41524821577179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074937113/2000000000 : ℝ)|^2079 ≤ (21939104534583/50000000000000 : ℝ)^1567
        have hw : |(1074937113/2000000000 : ℝ)|=(1074937113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-234466931/1000000000 : ℝ)|^2079 ≤ (1459696933401/10000000000000 : ℝ)^1567
        have hw : |(-234466931/1000000000 : ℝ)|=(234466931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5155941447/10000000000 : ℝ)|^2079 ≤ (41524821577179/100000000000000 : ℝ)^1567
        have hw : |(5155941447/10000000000 : ℝ)|=(5155941447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s2_2 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (335917843/625000000 : ℝ)*x 0 + (1031188299/2000000000 : ℝ)*x 1 + (-2344669349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335917843/625000000 : ℝ)^2079 ≤ (8775641647031/20000000000000 : ℝ)^1567 := by
    have hnat : (335917843 : ℕ)^2079*20000000000000^1567 ≤ 8775641647031^1567*625000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335917843 625000000 8775641647031 20000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031188299/2000000000 : ℝ)^2079 ≤ (5190602761259/12500000000000 : ℝ)^1567 := by
    have hnat : (1031188299 : ℕ)^2079*12500000000000^1567 ≤ 5190602761259^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031188299 2000000000 5190602761259 12500000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2344669349/10000000000 : ℝ)^2079 ≤ (729848482807/5000000000000 : ℝ)^1567 := by
    have hnat : (2344669349 : ℕ)^2079*5000000000000^1567 ≤ 729848482807^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2344669349 10000000000 729848482807 5000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335917843/625000000 : ℝ), (1031188299/2000000000 : ℝ), (-2344669349/10000000000 : ℝ)] ![(8775641647031/20000000000000 : ℝ), (5190602761259/12500000000000 : ℝ), (729848482807/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335917843/625000000 : ℝ)|^2079 ≤ (8775641647031/20000000000000 : ℝ)^1567
        have hw : |(335917843/625000000 : ℝ)|=(335917843/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031188299/2000000000 : ℝ)|^2079 ≤ (5190602761259/12500000000000 : ℝ)^1567
        have hw : |(1031188299/2000000000 : ℝ)|=(1031188299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2344669349/10000000000 : ℝ)|^2079 ≤ (729848482807/5000000000000 : ℝ)^1567
        have hw : |(-2344669349/10000000000 : ℝ)|=(2344669349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s2_3 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (68065921/156250000 : ℝ)*x 0 + (501917079/1250000000 : ℝ)*x 1 + (945189199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68065921/156250000 : ℝ)^2079 ≤ (33204180523579/100000000000000 : ℝ)^1567 := by
    have hnat : (68065921 : ℕ)^2079*100000000000000^1567 ≤ 33204180523579^1567*156250000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68065921 156250000 33204180523579 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501917079/1250000000 : ℝ)^2079 ≤ (14900899249531/50000000000000 : ℝ)^1567 := by
    have hnat : (501917079 : ℕ)^2079*50000000000000^1567 ≤ 14900899249531^1567*1250000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501917079 1250000000 14900899249531 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945189199/2000000000 : ℝ)^2079 ≤ (36994020965311/100000000000000 : ℝ)^1567 := by
    have hnat : (945189199 : ℕ)^2079*100000000000000^1567 ≤ 36994020965311^1567*2000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945189199 2000000000 36994020965311 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68065921/156250000 : ℝ), (501917079/1250000000 : ℝ), (945189199/2000000000 : ℝ)] ![(33204180523579/100000000000000 : ℝ), (14900899249531/50000000000000 : ℝ), (36994020965311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68065921/156250000 : ℝ)|^2079 ≤ (33204180523579/100000000000000 : ℝ)^1567
        have hw : |(68065921/156250000 : ℝ)|=(68065921/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501917079/1250000000 : ℝ)|^2079 ≤ (14900899249531/50000000000000 : ℝ)^1567
        have hw : |(501917079/1250000000 : ℝ)|=(501917079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(945189199/2000000000 : ℝ)|^2079 ≤ (36994020965311/100000000000000 : ℝ)^1567
        have hw : |(945189199/2000000000 : ℝ)|=(945189199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s2_4 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158241693/10000000000 : ℝ)*x 0 + (5158445383/10000000000 : ℝ)*x 1 + (2755965513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158241693/10000000000 : ℝ)^2079 ≤ (6538748196477/50000000000000 : ℝ)^1567 := by
    have hnat : (2158241693 : ℕ)^2079*50000000000000^1567 ≤ 6538748196477^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158241693 10000000000 6538748196477 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5158445383/10000000000 : ℝ)^2079 ≤ (10387894729751/25000000000000 : ℝ)^1567 := by
    have hnat : (5158445383 : ℕ)^2079*25000000000000^1567 ≤ 10387894729751^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158445383 10000000000 10387894729751 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755965513/5000000000 : ℝ)^2079 ≤ (1417841396101/3125000000000 : ℝ)^1567 := by
    have hnat : (2755965513 : ℕ)^2079*3125000000000^1567 ≤ 1417841396101^1567*5000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755965513 5000000000 1417841396101 3125000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158241693/10000000000 : ℝ), (5158445383/10000000000 : ℝ), (2755965513/5000000000 : ℝ)] ![(6538748196477/50000000000000 : ℝ), (10387894729751/25000000000000 : ℝ), (1417841396101/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158241693/10000000000 : ℝ)|^2079 ≤ (6538748196477/50000000000000 : ℝ)^1567
        have hw : |(-2158241693/10000000000 : ℝ)|=(2158241693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5158445383/10000000000 : ℝ)|^2079 ≤ (10387894729751/25000000000000 : ℝ)^1567
        have hw : |(5158445383/10000000000 : ℝ)|=(5158445383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755965513/5000000000 : ℝ)|^2079 ≤ (1417841396101/3125000000000 : ℝ)^1567
        have hw : |(2755965513/5000000000 : ℝ)|=(2755965513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s2_5 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5283834927/10000000000 : ℝ)*x 0 + (-124292381/625000000 : ℝ)*x 1 + (110238631/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283834927/10000000000 : ℝ)^2079 ≤ (42896904670837/100000000000000 : ℝ)^1567 := by
    have hnat : (5283834927 : ℕ)^2079*100000000000000^1567 ≤ 42896904670837^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283834927 10000000000 42896904670837 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124292381/625000000 : ℝ)^2079 ≤ (11732164915663/100000000000000 : ℝ)^1567 := by
    have hnat : (124292381 : ℕ)^2079*100000000000000^1567 ≤ 11732164915663^1567*625000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124292381 625000000 11732164915663 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110238631/200000000 : ℝ)^2079 ≤ (11342732599449/25000000000000 : ℝ)^1567 := by
    have hnat : (110238631 : ℕ)^2079*25000000000000^1567 ≤ 11342732599449^1567*200000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110238631 200000000 11342732599449 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283834927/10000000000 : ℝ), (-124292381/625000000 : ℝ), (110238631/200000000 : ℝ)] ![(42896904670837/100000000000000 : ℝ), (11732164915663/100000000000000 : ℝ), (11342732599449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283834927/10000000000 : ℝ)|^2079 ≤ (42896904670837/100000000000000 : ℝ)^1567
        have hw : |(5283834927/10000000000 : ℝ)|=(5283834927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-124292381/625000000 : ℝ)|^2079 ≤ (11732164915663/100000000000000 : ℝ)^1567
        have hw : |(-124292381/625000000 : ℝ)|=(124292381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110238631/200000000 : ℝ)|^2079 ≤ (11342732599449/25000000000000 : ℝ)^1567
        have hw : |(110238631/200000000 : ℝ)|=(110238631/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s2_6 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5283833751/10000000000 : ℝ)*x 0 + (5511931443/10000000000 : ℝ)*x 1 + (-248584983/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283833751/10000000000 : ℝ)^2079 ≤ (21448446001981/50000000000000 : ℝ)^1567 := by
    have hnat : (5283833751 : ℕ)^2079*50000000000000^1567 ≤ 21448446001981^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283833751 10000000000 21448446001981 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5511931443/10000000000 : ℝ)^2079 ≤ (45370929229257/100000000000000 : ℝ)^1567 := by
    have hnat : (5511931443 : ℕ)^2079*100000000000000^1567 ≤ 45370929229257^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511931443 10000000000 45370929229257 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248584983/1250000000 : ℝ)^2079 ≤ (11732178753923/100000000000000 : ℝ)^1567 := by
    have hnat : (248584983 : ℕ)^2079*100000000000000^1567 ≤ 11732178753923^1567*1250000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248584983 1250000000 11732178753923 100000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283833751/10000000000 : ℝ), (5511931443/10000000000 : ℝ), (-248584983/1250000000 : ℝ)] ![(21448446001981/50000000000000 : ℝ), (45370929229257/100000000000000 : ℝ), (11732178753923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283833751/10000000000 : ℝ)|^2079 ≤ (21448446001981/50000000000000 : ℝ)^1567
        have hw : |(5283833751/10000000000 : ℝ)|=(5283833751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5511931443/10000000000 : ℝ)|^2079 ≤ (45370929229257/100000000000000 : ℝ)^1567
        have hw : |(5511931443/10000000000 : ℝ)|=(5511931443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-248584983/1250000000 : ℝ)|^2079 ≤ (11732178753923/100000000000000 : ℝ)^1567
        have hw : |(-248584983/1250000000 : ℝ)|=(248584983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1123_s2_7 (p : ℝ) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4356432637/10000000000 : ℝ)*x 0 + (4720981169/10000000000 : ℝ)*x 1 + (4020351571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356432637/10000000000 : ℝ)^2079 ≤ (8301585390311/25000000000000 : ℝ)^1567 := by
    have hnat : (4356432637 : ℕ)^2079*25000000000000^1567 ≤ 8301585390311^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356432637 10000000000 8301585390311 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4720981169/10000000000 : ℝ)^2079 ≤ (18471233756789/50000000000000 : ℝ)^1567 := by
    have hnat : (4720981169 : ℕ)^2079*50000000000000^1567 ≤ 18471233756789^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4720981169 10000000000 18471233756789 50000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020351571/10000000000 : ℝ)^2079 ≤ (7462797727919/25000000000000 : ℝ)^1567 := by
    have hnat : (4020351571 : ℕ)^2079*25000000000000^1567 ≤ 7462797727919^1567*10000000000^2079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020351571 10000000000 7462797727919 25000000000000 2079 1567 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2079/512 : ℝ)) 2079 1567 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356432637/10000000000 : ℝ), (4720981169/10000000000 : ℝ), (4020351571/10000000000 : ℝ)] ![(8301585390311/25000000000000 : ℝ), (18471233756789/50000000000000 : ℝ), (7462797727919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356432637/10000000000 : ℝ)|^2079 ≤ (8301585390311/25000000000000 : ℝ)^1567
        have hw : |(4356432637/10000000000 : ℝ)|=(4356432637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4720981169/10000000000 : ℝ)|^2079 ≤ (18471233756789/50000000000000 : ℝ)^1567
        have hw : |(4720981169/10000000000 : ℝ)|=(4720981169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020351571/10000000000 : ℝ)|^2079 ≤ (7462797727919/25000000000000 : ℝ)^1567
        have hw : |(4020351571/10000000000 : ℝ)|=(4020351571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1123_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5131/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5543/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8983/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (207/1250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5131/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5543/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5131/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5543/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5131/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5543/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5131/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5543/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5131/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5543/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5131/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5543/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (5543/100000 : ℝ) ^ (8315/2048 : ℝ) ≤ (793470159056893/100000000000000000000 : ℝ) := by
    have hpowers : (5543/100000 : ℝ)^8315 ≤ (793470159056893/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5543 : ℕ)^8315*100000000000000000000^2048 ≤ 793470159056893^2048*100000^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5543 100000 793470159056893 100000000000000000000 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5543/100000 : ℝ)) (X := (793470159056893/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5131/25000 : ℝ) ^ (8315/2048 : ℝ) ≤ (161340518070175519/100000000000000000000 : ℝ) := by
    have hpowers : (5131/25000 : ℝ)^8315 ≤ (161340518070175519/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5131 : ℕ)^8315*100000000000000000000^2048 ≤ 161340518070175519^2048*25000^8315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5131 25000 161340518070175519 100000000000000000000 8315 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5131/25000 : ℝ)) (X := (161340518070175519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000793470159056893/50000000000000000000 : ℝ) ≤ (10000039086402107/10000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (50000793470159056893/50000000000000000000 : ℝ)^2048 ≤ (10000039086402107/10000000000000000 : ℝ)^8315 := by
      have hnat : (50000793470159056893 : ℕ)^2048*10000000000000000^8315 ≤ 10000039086402107^8315*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000793470159056893 50000000000000000000 10000039086402107 10000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000039086402107/10000000000000000 : ℝ)) (X := (50000793470159056893/50000000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25040533497057308103/25000000000000000000 : ℝ) ≤ (5001995476350137/5000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (25040533497057308103/25000000000000000000 : ℝ)^2048 ≤ (5001995476350137/5000000000000000 : ℝ)^8315 := by
      have hnat : (25040533497057308103 : ℕ)^2048*5000000000000000^8315 ≤ 5001995476350137^8315*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25040533497057308103 25000000000000000000 5001995476350137 5000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001995476350137/5000000000000000 : ℝ)) (X := (25040533497057308103/25000000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50161340518070175519/50000000000000000000 : ℝ) ≤ (10007942818998441/10000000000000000 : ℝ) ^ (8315/2048 : ℝ) := by
    have hpowers : (50161340518070175519/50000000000000000000 : ℝ)^2048 ≤ (10007942818998441/10000000000000000 : ℝ)^8315 := by
      have hnat : (50161340518070175519 : ℕ)^2048*10000000000000000^8315 ≤ 10007942818998441^8315*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50161340518070175519 50000000000000000000 10007942818998441 10000000000000000 2048 8315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007942818998441/10000000000000000 : ℝ)) (X := (50161340518070175519/50000000000000000000 : ℝ)) (by norm_num) 8315 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(793470159056893/100000000000000000000 : ℝ) ≤ ((29953355032721697121/29962000000000000000 : ℝ)+2*(3951866298167/1498100000000000 : ℝ)*(5543/100000 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (29953355032721697121/29962000000000000000 : ℝ)+2*(3951866298167/1498100000000000 : ℝ)*(5543/100000 : ℝ)=(10000039086402107/10000000000000000 : ℝ) by norm_num, show 1+2*(793470159056893/100000000000000000000 : ℝ)=(50000793470159056893/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(161340518070175519/100000000000000000000 : ℝ)+(793470159056893/100000000000000000000 : ℝ) ≤ ((29953355032721697121/29962000000000000000 : ℝ)+(3951866298167/1498100000000000 : ℝ)*((5131/25000 : ℝ)+(5543/100000 : ℝ)))^(8315/2048 : ℝ) := by
    rw [show (29953355032721697121/29962000000000000000 : ℝ)+(3951866298167/1498100000000000 : ℝ)*((5131/25000 : ℝ)+(5543/100000 : ℝ))=(5001995476350137/5000000000000000 : ℝ) by norm_num, show 1+(161340518070175519/100000000000000000000 : ℝ)+(793470159056893/100000000000000000000 : ℝ)=(25040533497057308103/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(161340518070175519/100000000000000000000 : ℝ) ≤ ((29953355032721697121/29962000000000000000 : ℝ)+2*(3951866298167/1498100000000000 : ℝ)*(5131/25000 : ℝ))^(8315/2048 : ℝ) := by
    rw [show (29953355032721697121/29962000000000000000 : ℝ)+2*(3951866298167/1498100000000000 : ℝ)*(5131/25000 : ℝ)=(10007942818998441/10000000000000000 : ℝ) by norm_num, show 1+2*(161340518070175519/100000000000000000000 : ℝ)=(50161340518070175519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29953355032721697121/29962000000000000000 : ℝ)*(X 1 0+X 2 0)+(3951866298167/1498100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (5543/100000 : ℝ)) (hi := (5131/25000 : ℝ)) (c := (29953355032721697121/29962000000000000000 : ℝ)) (alpha := (3951866298167/1498100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29953355032721697121/29962000000000000000 : ℝ)*(X 0 1+X 2 1)+(3951866298167/1498100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (5543/100000 : ℝ)) (hi := (5131/25000 : ℝ)) (c := (29953355032721697121/29962000000000000000 : ℝ)) (alpha := (3951866298167/1498100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29953355032721697121/29962000000000000000 : ℝ)*(X 0 2+X 1 2)+(3951866298167/1498100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8315/2048 : ℝ)) (lo := (5543/100000 : ℝ)) (hi := (5131/25000 : ℝ)) (c := (29953355032721697121/29962000000000000000 : ℝ)) (alpha := (3951866298167/1498100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2158133683/10000000000 : ℝ)*X 0 0+(1378615487/2500000000 : ℝ)*X 0 1+(5155939909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074937113/2000000000 : ℝ)*X 1 0+(-234466931/1000000000 : ℝ)*X 1 1+(5155941447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335917843/625000000 : ℝ)*X 2 0+(1031188299/2000000000 : ℝ)*X 2 1+(-2344669349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((68065921/156250000 : ℝ)*X 0 0+(501917079/1250000000 : ℝ)*X 0 1+(945189199/2000000000 : ℝ)*X 0 2+(68065921/156250000 : ℝ)*X 1 0+(501917079/1250000000 : ℝ)*X 1 1+(945189199/2000000000 : ℝ)*X 1 2+(68065921/156250000 : ℝ)*X 2 0+(501917079/1250000000 : ℝ)*X 2 1+(945189199/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2158241693/10000000000 : ℝ)*X 0 0+(5158445383/10000000000 : ℝ)*X 0 1+(2755965513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5283834927/10000000000 : ℝ)*X 1 0+(-124292381/625000000 : ℝ)*X 1 1+(110238631/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5283833751/10000000000 : ℝ)*X 2 0+(5511931443/10000000000 : ℝ)*X 2 1+(-248584983/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356432637/10000000000 : ℝ)*X 0 0+(4720981169/10000000000 : ℝ)*X 0 1+(4020351571/10000000000 : ℝ)*X 0 2+(4356432637/10000000000 : ℝ)*X 1 0+(4720981169/10000000000 : ℝ)*X 1 1+(4020351571/10000000000 : ℝ)*X 1 2+(4356432637/10000000000 : ℝ)*X 2 0+(4720981169/10000000000 : ℝ)*X 2 1+(4020351571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1123_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10316335433367571025817/936312500000000000000000000 : ℝ) := by norm_num
    linear_combination (1400779043/100000000000000 : ℝ)*(base19) + (1113451361/100000000000000 : ℝ)*(base23) + (298921859/100000000000000 : ℝ)*(upper3) + (33238043/25000000000000 : ℝ)*(upper4) + (76521891/100000000000000 : ℝ)*(upper5) + (419653676242563/20000000000000 : ℝ)*(major0) + (419653676242563/20000000000000 : ℝ)*(major1) + (419653676242563/20000000000000 : ℝ)*(major2) + (1394626949679467/50000000000000 : ℝ)*(sp0) + (1394637606517921/50000000000000 : ℝ)*(sp1) + (697318875090881/25000000000000 : ℝ)*(sp2) + (281450054630971/20000000000000 : ℝ)*(sp3) + (454289119/2000000000000 : ℝ)*(sp4) + (237704691/2500000000000 : ℝ)*(sp7) + (703629890671247/50000000000000 : ℝ)*(f.failure) + (697319153453721/25000000000000 : ℝ)*(f.sum) + (21626363730053/14981000000000000000000000000 : ℝ)*base65 + (108113068824701123/599240000000000000000000000000000 : ℝ)*base67 + (593547874842858877/599240000000000000000000000000000 : ℝ)*base70 + (210416083857981123/599240000000000000000000000000000 : ℝ)*base71 + (26974461301521/14981000000000000000000000000 : ℝ)*base73 + (3962919591975178877/599240000000000000000000000000000 : ℝ)*base76 + (6586355142915698877/599240000000000000000000000000000 : ℝ)*base78 + (2981585062659181123/599240000000000000000000000000000 : ℝ)*base79 + (291874993141/468156250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2129689/500000000000000000000 : ℝ)*base90 + (2129689/500000000000000000000 : ℝ)*base92 + (2129689/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6611199411933003325453863243/749050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (160973037/10000000000000 : ℝ)*(base19) + (1129379411/100000000000000 : ℝ)*(base23) + (103649269/50000000000000 : ℝ)*(upper2) + (99538979/100000000000000 : ℝ)*(upper3) + (7920997/3125000000000 : ℝ)*(upper5) + (2128125375062761/100000000000000 : ℝ)*(major0) + (2128125375062761/100000000000000 : ℝ)*(major1) + (2128125375062761/100000000000000 : ℝ)*(major2) + (34659699/160000000000 : ℝ)*(sp1) + (752673907/10000000000000 : ℝ)*(sp2) + (2828966283508521/100000000000000 : ℝ)*(sp4) + (707235752866569/25000000000000 : ℝ)*(sp5) + (70723940684751/2500000000000 : ℝ)*(sp6) + (178410521551657/12500000000000 : ℝ)*(sp7) + (178410521551657/12500000000000 : ℝ)*(f.failure) + (2828966283508521/100000000000000 : ℝ)*(f.sum) + (10026983628527/18726250000000000000000000000 : ℝ)*base66 + (1316887761743648919/2996200000000000000000000000000000 : ℝ)*base68 + (6475483997666648919/2996200000000000000000000000000000 : ℝ)*base70 + (10386557419274048919/2996200000000000000000000000000000 : ℝ)*base72 + (47518968213297/74905000000000000000000000000 : ℝ)*base73 + (12811299955173551081/2996200000000000000000000000000000 : ℝ)*base75 + (1945812508376648919/2996200000000000000000000000000000 : ℝ)*base78 + (11378513353201048919/2996200000000000000000000000000000 : ℝ)*base80 + (92693878698243/74905000000000000000000000000 : ℝ)*base82 + (288641/125000000000000000000 : ℝ)*base89 + (288641/125000000000000000000 : ℝ)*base91 + (288641/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1123_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5131/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5543/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8983/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (207/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1123_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1123_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8983/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (207/1250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1123_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1123_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1123_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8315/2048 : ℝ) ≤ p) (hpb : p ≤ (2079/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14910313/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8983/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (207/1250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1123_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
