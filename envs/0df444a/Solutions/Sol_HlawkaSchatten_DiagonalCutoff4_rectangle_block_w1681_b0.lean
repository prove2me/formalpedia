-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1681_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:32:24.999154+00:00
-- url     : https://prove2.me/submissions/670845d4-0f3c-4b17-916e-3b9f098cc102

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
theorem support_rectangle_w1681_s0_0 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1426527143/10000000000 : ℝ)*x 0 + (719977677/1250000000 : ℝ)*x 1 + (4926995017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1426527143/10000000000 : ℝ)^5071 ≤ (8715455932157/100000000000000 : ℝ)^4047 := by
    have hnat : (1426527143 : ℕ)^5071*100000000000000^4047 ≤ 8715455932157^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426527143 10000000000 8715455932157 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (719977677/1250000000 : ℝ)^5071 ≤ (25047019345287/50000000000000 : ℝ)^4047 := by
    have hnat : (719977677 : ℕ)^5071*50000000000000^4047 ≤ 25047019345287^4047*1250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719977677 1250000000 25047019345287 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4926995017/10000000000 : ℝ)^5071 ≤ (2574406585259/6250000000000 : ℝ)^4047 := by
    have hnat : (4926995017 : ℕ)^5071*6250000000000^4047 ≤ 2574406585259^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4926995017 10000000000 2574406585259 6250000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1426527143/10000000000 : ℝ), (719977677/1250000000 : ℝ), (4926995017/10000000000 : ℝ)] ![(8715455932157/100000000000000 : ℝ), (25047019345287/50000000000000 : ℝ), (2574406585259/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1426527143/10000000000 : ℝ)|^5071 ≤ (8715455932157/100000000000000 : ℝ)^4047
        have hw : |(-1426527143/10000000000 : ℝ)|=(1426527143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(719977677/1250000000 : ℝ)|^5071 ≤ (25047019345287/50000000000000 : ℝ)^4047
        have hw : |(719977677/1250000000 : ℝ)|=(719977677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4926995017/10000000000 : ℝ)|^5071 ≤ (2574406585259/6250000000000 : ℝ)^4047
        have hw : |(4926995017/10000000000 : ℝ)|=(4926995017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s0_1 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2712637421/5000000000 : ℝ)*x 0 + (-1882095019/10000000000 : ℝ)*x 1 + (1231749003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2712637421/5000000000 : ℝ)^5071 ≤ (4647541672317/10000000000000 : ℝ)^4047 := by
    have hnat : (2712637421 : ℕ)^5071*10000000000000^4047 ≤ 4647541672317^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712637421 5000000000 4647541672317 10000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1882095019/10000000000 : ℝ)^5071 ≤ (12334067471591/100000000000000 : ℝ)^4047 := by
    have hnat : (1882095019 : ℕ)^5071*100000000000000^4047 ≤ 12334067471591^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882095019 10000000000 12334067471591 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1231749003/2500000000 : ℝ)^5071 ≤ (20595257893641/50000000000000 : ℝ)^4047 := by
    have hnat : (1231749003 : ℕ)^5071*50000000000000^4047 ≤ 20595257893641^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231749003 2500000000 20595257893641 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2712637421/5000000000 : ℝ), (-1882095019/10000000000 : ℝ), (1231749003/2500000000 : ℝ)] ![(4647541672317/10000000000000 : ℝ), (12334067471591/100000000000000 : ℝ), (20595257893641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2712637421/5000000000 : ℝ)|^5071 ≤ (4647541672317/10000000000000 : ℝ)^4047
        have hw : |(2712637421/5000000000 : ℝ)|=(2712637421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1882095019/10000000000 : ℝ)|^5071 ≤ (12334067471591/100000000000000 : ℝ)^4047
        have hw : |(-1882095019/10000000000 : ℝ)|=(1882095019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1231749003/2500000000 : ℝ)|^5071 ≤ (20595257893641/50000000000000 : ℝ)^4047
        have hw : |(1231749003/2500000000 : ℝ)|=(1231749003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s0_2 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5425276497/10000000000 : ℝ)*x 0 + (153968593/312500000 : ℝ)*x 1 + (-941047089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5425276497/10000000000 : ℝ)^5071 ≤ (11618858621989/25000000000000 : ℝ)^4047 := by
    have hnat : (5425276497 : ℕ)^5071*25000000000000^4047 ≤ 11618858621989^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425276497 10000000000 11618858621989 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153968593/312500000 : ℝ)^5071 ≤ (5148813116831/12500000000000 : ℝ)^4047 := by
    have hnat : (153968593 : ℕ)^5071*12500000000000^4047 ≤ 5148813116831^4047*312500000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153968593 312500000 5148813116831 12500000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941047089/5000000000 : ℝ)^5071 ≤ (12334060565677/100000000000000 : ℝ)^4047 := by
    have hnat : (941047089 : ℕ)^5071*100000000000000^4047 ≤ 12334060565677^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941047089 5000000000 12334060565677 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5425276497/10000000000 : ℝ), (153968593/312500000 : ℝ), (-941047089/5000000000 : ℝ)] ![(11618858621989/25000000000000 : ℝ), (5148813116831/12500000000000 : ℝ), (12334060565677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5425276497/10000000000 : ℝ)|^5071 ≤ (11618858621989/25000000000000 : ℝ)^4047
        have hw : |(5425276497/10000000000 : ℝ)|=(5425276497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(153968593/312500000 : ℝ)|^5071 ≤ (5148813116831/12500000000000 : ℝ)^4047
        have hw : |(153968593/312500000 : ℝ)|=(153968593/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-941047089/5000000000 : ℝ)|^5071 ≤ (12334060565677/100000000000000 : ℝ)^4047
        have hw : |(-941047089/5000000000 : ℝ)|=(941047089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s0_3 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4064526487/10000000000 : ℝ)*x 0 + (1521415347/5000000000 : ℝ)*x 1 + (2649152407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4064526487/10000000000 : ℝ)^5071 ≤ (32365248559497/100000000000000 : ℝ)^4047 := by
    have hnat : (4064526487 : ℕ)^5071*100000000000000^4047 ≤ 32365248559497^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4064526487 10000000000 32365248559497 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1521415347/5000000000 : ℝ)^5071 ≤ (5629543255761/25000000000000 : ℝ)^4047 := by
    have hnat : (1521415347 : ℕ)^5071*25000000000000^4047 ≤ 5629543255761^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521415347 5000000000 5629543255761 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2649152407/5000000000 : ℝ)^5071 ≤ (45116578393297/100000000000000 : ℝ)^4047 := by
    have hnat : (2649152407 : ℕ)^5071*100000000000000^4047 ≤ 45116578393297^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2649152407 5000000000 45116578393297 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4064526487/10000000000 : ℝ), (1521415347/5000000000 : ℝ), (2649152407/5000000000 : ℝ)] ![(32365248559497/100000000000000 : ℝ), (5629543255761/25000000000000 : ℝ), (45116578393297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4064526487/10000000000 : ℝ)|^5071 ≤ (32365248559497/100000000000000 : ℝ)^4047
        have hw : |(4064526487/10000000000 : ℝ)|=(4064526487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1521415347/5000000000 : ℝ)|^5071 ≤ (5629543255761/25000000000000 : ℝ)^4047
        have hw : |(1521415347/5000000000 : ℝ)|=(1521415347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2649152407/5000000000 : ℝ)|^5071 ≤ (45116578393297/100000000000000 : ℝ)^4047
        have hw : |(2649152407/5000000000 : ℝ)|=(2649152407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s0_4 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-714356463/5000000000 : ℝ)*x 0 + (1237022747/2500000000 : ℝ)*x 1 + (286899281/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (714356463/5000000000 : ℝ)^5071 ≤ (8732192317599/100000000000000 : ℝ)^4047 := by
    have hnat : (714356463 : ℕ)^5071*100000000000000^4047 ≤ 8732192317599^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714356463 5000000000 8732192317599 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1237022747/2500000000 : ℝ)^5071 ≤ (10352904029351/25000000000000 : ℝ)^4047 := by
    have hnat : (1237022747 : ℕ)^5071*25000000000000^4047 ≤ 10352904029351^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237022747 2500000000 10352904029351 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286899281/500000000 : ℝ)^5071 ≤ (12464047889513/25000000000000 : ℝ)^4047 := by
    have hnat : (286899281 : ℕ)^5071*25000000000000^4047 ≤ 12464047889513^4047*500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286899281 500000000 12464047889513 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-714356463/5000000000 : ℝ), (1237022747/2500000000 : ℝ), (286899281/500000000 : ℝ)] ![(8732192317599/100000000000000 : ℝ), (10352904029351/25000000000000 : ℝ), (12464047889513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-714356463/5000000000 : ℝ)|^5071 ≤ (8732192317599/100000000000000 : ℝ)^4047
        have hw : |(-714356463/5000000000 : ℝ)|=(714356463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1237022747/2500000000 : ℝ)|^5071 ≤ (10352904029351/25000000000000 : ℝ)^4047
        have hw : |(1237022747/2500000000 : ℝ)|=(1237022747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(286899281/500000000 : ℝ)|^5071 ≤ (12464047889513/25000000000000 : ℝ)^4047
        have hw : |(286899281/500000000 : ℝ)|=(286899281/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s0_5 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198809483/10000000000 : ℝ)*x 0 + (-267776207/2500000000 : ℝ)*x 1 + (5737985597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198809483/10000000000 : ℝ)^5071 ≤ (275359430899/625000000000 : ℝ)^4047 := by
    have hnat : (5198809483 : ℕ)^5071*625000000000^4047 ≤ 275359430899^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198809483 10000000000 275359430899 625000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267776207/2500000000 : ℝ)^5071 ≤ (3043149871259/50000000000000 : ℝ)^4047 := by
    have hnat : (267776207 : ℕ)^5071*50000000000000^4047 ≤ 3043149871259^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267776207 2500000000 3043149871259 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5737985597/10000000000 : ℝ)^5071 ≤ (12464047826911/25000000000000 : ℝ)^4047 := by
    have hnat : (5737985597 : ℕ)^5071*25000000000000^4047 ≤ 12464047826911^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5737985597 10000000000 12464047826911 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198809483/10000000000 : ℝ), (-267776207/2500000000 : ℝ), (5737985597/10000000000 : ℝ)] ![(275359430899/625000000000 : ℝ), (3043149871259/50000000000000 : ℝ), (12464047826911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198809483/10000000000 : ℝ)|^5071 ≤ (275359430899/625000000000 : ℝ)^4047
        have hw : |(5198809483/10000000000 : ℝ)|=(5198809483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267776207/2500000000 : ℝ)|^5071 ≤ (3043149871259/50000000000000 : ℝ)^4047
        have hw : |(-267776207/2500000000 : ℝ)|=(267776207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5737985597/10000000000 : ℝ)|^5071 ≤ (12464047826911/25000000000000 : ℝ)^4047
        have hw : |(5737985597/10000000000 : ℝ)|=(5737985597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s0_6 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599404721/5000000000 : ℝ)*x 0 + (2868992707/5000000000 : ℝ)*x 1 + (-66944073/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599404721/5000000000 : ℝ)^5071 ≤ (11014377127117/25000000000000 : ℝ)^4047 := by
    have hnat : (2599404721 : ℕ)^5071*25000000000000^4047 ≤ 11014377127117^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599404721 5000000000 11014377127117 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2868992707/5000000000 : ℝ)^5071 ≤ (49856189315269/100000000000000 : ℝ)^4047 := by
    have hnat : (2868992707 : ℕ)^5071*100000000000000^4047 ≤ 49856189315269^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2868992707 5000000000 49856189315269 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66944073/625000000 : ℝ)^5071 ≤ (47549235651/781250000000 : ℝ)^4047 := by
    have hnat : (66944073 : ℕ)^5071*781250000000^4047 ≤ 47549235651^4047*625000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66944073 625000000 47549235651 781250000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599404721/5000000000 : ℝ), (2868992707/5000000000 : ℝ), (-66944073/625000000 : ℝ)] ![(11014377127117/25000000000000 : ℝ), (49856189315269/100000000000000 : ℝ), (47549235651/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599404721/5000000000 : ℝ)|^5071 ≤ (11014377127117/25000000000000 : ℝ)^4047
        have hw : |(2599404721/5000000000 : ℝ)|=(2599404721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2868992707/5000000000 : ℝ)|^5071 ≤ (49856189315269/100000000000000 : ℝ)^4047
        have hw : |(2868992707/5000000000 : ℝ)|=(2868992707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66944073/625000000 : ℝ)|^5071 ≤ (47549235651/781250000000 : ℝ)^4047
        have hw : |(-66944073/625000000 : ℝ)|=(66944073/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s0_7 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4070446137/10000000000 : ℝ)*x 0 + (5241171471/10000000000 : ℝ)*x 1 + (3101965907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4070446137/10000000000 : ℝ)^5071 ≤ (32424323787949/100000000000000 : ℝ)^4047 := by
    have hnat : (4070446137 : ℕ)^5071*100000000000000^4047 ≤ 32424323787949^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4070446137 10000000000 32424323787949 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241171471/10000000000 : ℝ)^5071 ≤ (44507806247471/100000000000000 : ℝ)^4047 := by
    have hnat : (5241171471 : ℕ)^5071*100000000000000^4047 ≤ 44507806247471^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241171471 10000000000 44507806247471 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3101965907/10000000000 : ℝ)^5071 ≤ (288348374423/1250000000000 : ℝ)^4047 := by
    have hnat : (3101965907 : ℕ)^5071*1250000000000^4047 ≤ 288348374423^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3101965907 10000000000 288348374423 1250000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4070446137/10000000000 : ℝ), (5241171471/10000000000 : ℝ), (3101965907/10000000000 : ℝ)] ![(32424323787949/100000000000000 : ℝ), (44507806247471/100000000000000 : ℝ), (288348374423/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4070446137/10000000000 : ℝ)|^5071 ≤ (32424323787949/100000000000000 : ℝ)^4047
        have hw : |(4070446137/10000000000 : ℝ)|=(4070446137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241171471/10000000000 : ℝ)|^5071 ≤ (44507806247471/100000000000000 : ℝ)^4047
        have hw : |(5241171471/10000000000 : ℝ)|=(5241171471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3101965907/10000000000 : ℝ)|^5071 ≤ (288348374423/1250000000000 : ℝ)^4047
        have hw : |(3101965907/10000000000 : ℝ)|=(3101965907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1681_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (641/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22987/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5063/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5063 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5063*1^1024 ≤ 0^1024*1^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5063/1024 : ℝ) ≤ (1077583453655018657/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5063 ≤ (1077583453655018657/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5063*100000000000000000000^1024 ≤ 1077583453655018657^1024*5^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1077583453655018657 100000000000000000000 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1077583453655018657/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5063 := by
      have hnat : (1 : ℕ)^1024*1^5063 ≤ 1^5063*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101077583453655018657/100000000000000000000 : ℝ) ≤ (10021701225010759/10000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (101077583453655018657/100000000000000000000 : ℝ)^1024 ≤ (10021701225010759/10000000000000000 : ℝ)^5063 := by
      have hnat : (101077583453655018657 : ℕ)^1024*10000000000000000^5063 ≤ 10021701225010759^5063*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101077583453655018657 100000000000000000000 10021701225010759 10000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10021701225010759/10000000000000000 : ℝ)) (X := (101077583453655018657/100000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51077583453655018657/50000000000000000000 : ℝ) ≤ (5021701225010759/5000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (51077583453655018657/50000000000000000000 : ℝ)^1024 ≤ (5021701225010759/5000000000000000 : ℝ)^5063 := by
      have hnat : (51077583453655018657 : ℕ)^1024*5000000000000000^5063 ≤ 5021701225010759^5063*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51077583453655018657 50000000000000000000 5021701225010759 5000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5021701225010759/5000000000000000 : ℝ)) (X := (51077583453655018657/50000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(21701225010759/4000000000000000 : ℝ)*(0 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21701225010759/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1077583453655018657/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(21701225010759/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5063/1024 : ℝ) := by
    rw [show (1 : ℝ)+(21701225010759/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10021701225010759/10000000000000000 : ℝ) by norm_num, show 1+(1077583453655018657/100000000000000000000 : ℝ)+(0 : ℝ)=(101077583453655018657/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1077583453655018657/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(21701225010759/4000000000000000 : ℝ)*(2/5 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21701225010759/4000000000000000 : ℝ)*(2/5 : ℝ)=(5021701225010759/5000000000000000 : ℝ) by norm_num, show 1+2*(1077583453655018657/100000000000000000000 : ℝ)=(51077583453655018657/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(21701225010759/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21701225010759/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(21701225010759/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21701225010759/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(21701225010759/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21701225010759/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1426527143/10000000000 : ℝ)*X 0 0+(719977677/1250000000 : ℝ)*X 0 1+(4926995017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2712637421/5000000000 : ℝ)*X 1 0+(-1882095019/10000000000 : ℝ)*X 1 1+(1231749003/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5425276497/10000000000 : ℝ)*X 2 0+(153968593/312500000 : ℝ)*X 2 1+(-941047089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4064526487/10000000000 : ℝ)*X 0 0+(1521415347/5000000000 : ℝ)*X 0 1+(2649152407/5000000000 : ℝ)*X 0 2+(4064526487/10000000000 : ℝ)*X 1 0+(1521415347/5000000000 : ℝ)*X 1 1+(2649152407/5000000000 : ℝ)*X 1 2+(4064526487/10000000000 : ℝ)*X 2 0+(1521415347/5000000000 : ℝ)*X 2 1+(2649152407/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-714356463/5000000000 : ℝ)*X 0 0+(1237022747/2500000000 : ℝ)*X 0 1+(286899281/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5198809483/10000000000 : ℝ)*X 1 0+(-267776207/2500000000 : ℝ)*X 1 1+(5737985597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2599404721/5000000000 : ℝ)*X 2 0+(2868992707/5000000000 : ℝ)*X 2 1+(-66944073/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4070446137/10000000000 : ℝ)*X 0 0+(5241171471/10000000000 : ℝ)*X 0 1+(3101965907/10000000000 : ℝ)*X 0 2+(4070446137/10000000000 : ℝ)*X 1 0+(5241171471/10000000000 : ℝ)*X 1 1+(3101965907/10000000000 : ℝ)*X 1 2+(4070446137/10000000000 : ℝ)*X 2 0+(5241171471/10000000000 : ℝ)*X 2 1+(3101965907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (470316204400751406299751/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57567959/100000000000000 : ℝ)*(base1) + (388762343/50000000000000 : ℝ)*(base19) + (1084676369/100000000000000 : ℝ)*(base23) + (1182761/2000000000000 : ℝ)*(base24) + (94223027/50000000000000 : ℝ)*(upper5) + (411027310992679/50000000000000 : ℝ)*(major0) + (411027310992679/50000000000000 : ℝ)*(major1) + (411027310992679/50000000000000 : ℝ)*(major2) + (1200733872947397/100000000000000 : ℝ)*(sp0) + (150092378119813/12500000000000 : ℝ)*(sp1) + (120073865866877/10000000000000 : ℝ)*(sp2) + (44336762502667/10000000000000 : ℝ)*(sp3) + (748387969/12500000000000 : ℝ)*(sp4) + (80106041/5000000000000 : ℝ)*(sp7) + (8867385694309/2000000000000 : ℝ)*(f.failure) + (120073980248319/10000000000000 : ℝ)*(f.sum) + (137622194533361/100000000000000000000000000000 : ℝ)*base65 + (1603575479633361/200000000000000000000000000000 : ℝ)*base67 + (1419082723433361/200000000000000000000000000000 : ℝ)*base69 + (1559603345633361/200000000000000000000000000000 : ℝ)*base71 + (156806382833361/100000000000000000000000000000 : ℝ)*base73 + (6381088366639/200000000000000000000000000000 : ℝ)*base76 + (1290854881233361/200000000000000000000000000000 : ℝ)*base77 + (1830803801233361/200000000000000000000000000000 : ℝ)*base79 + (39514460766639/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (670929/200000000000000000000 : ℝ)*base90 + (670929/200000000000000000000 : ℝ)*base92 + (670929/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24438426654400293875691/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (569661759/50000000000000 : ℝ)*(base19) + (1118136539/100000000000000 : ℝ)*(base23) + (90875967/100000000000000 : ℝ)*(base32) + (38778911/20000000000000 : ℝ)*(upper3) + (67119799/50000000000000 : ℝ)*(upper5) + (108340892372183/12500000000000 : ℝ)*(major0) + (108340892372183/12500000000000 : ℝ)*(major1) + (108340892372183/12500000000000 : ℝ)*(major2) + (222548319/6250000000000 : ℝ)*(sp1) + (3303572251/100000000000000 : ℝ)*(sp2) + (632995513787337/50000000000000 : ℝ)*(sp4) + (316496581869513/25000000000000 : ℝ)*(sp5) + (316496651466471/25000000000000 : ℝ)*(sp6) + (1460821864317/312500000000 : ℝ)*(sp7) + (467463087457407/100000000000000 : ℝ)*(f.failure) + (632995513787337/50000000000000 : ℝ)*(f.sum) + (20311321583103/25000000000000000000000000000 : ℝ)*base66 + (221941600283103/50000000000000000000000000000 : ℝ)*base68 + (99172490683103/50000000000000000000000000000 : ℝ)*base70 + (136680490883103/50000000000000000000000000000 : ℝ)*base72 + (94997147883103/25000000000000000000000000000 : ℝ)*base74 + (7512988716897/50000000000000000000000000000 : ℝ)*base75 + (156837730433103/50000000000000000000000000000 : ℝ)*base78 + (164231052283103/50000000000000000000000000000 : ℝ)*base80 + (2120364933103/25000000000000000000000000000 : ℝ)*base82 + (59486333/10000000000000000000000 : ℝ)*base89 + (59486333/10000000000000000000000 : ℝ)*base91 + (59486333/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1681_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (641/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22987/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1681_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1681_s1_0 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-303473321/2000000000 : ℝ)*x 0 + (5516299329/10000000000 : ℝ)*x 1 + (204447549/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (303473321/2000000000 : ℝ)^5071 ≤ (4708194241789/50000000000000 : ℝ)^4047 := by
    have hnat : (303473321 : ℕ)^5071*50000000000000^4047 ≤ 4708194241789^4047*2000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303473321 2000000000 4708194241789 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5516299329/10000000000 : ℝ)^5071 ≤ (23727269855207/50000000000000 : ℝ)^4047 := by
    have hnat : (5516299329 : ℕ)^5071*50000000000000^4047 ≤ 23727269855207^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516299329 10000000000 23727269855207 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204447549/400000000 : ℝ)^5071 ≤ (269556698741/625000000000 : ℝ)^4047 := by
    have hnat : (204447549 : ℕ)^5071*625000000000^4047 ≤ 269556698741^4047*400000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204447549 400000000 269556698741 625000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-303473321/2000000000 : ℝ), (5516299329/10000000000 : ℝ), (204447549/400000000 : ℝ)] ![(4708194241789/50000000000000 : ℝ), (23727269855207/50000000000000 : ℝ), (269556698741/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-303473321/2000000000 : ℝ)|^5071 ≤ (4708194241789/50000000000000 : ℝ)^4047
        have hw : |(-303473321/2000000000 : ℝ)|=(303473321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5516299329/10000000000 : ℝ)|^5071 ≤ (23727269855207/50000000000000 : ℝ)^4047
        have hw : |(5516299329/10000000000 : ℝ)|=(5516299329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204447549/400000000 : ℝ)|^5071 ≤ (269556698741/625000000000 : ℝ)^4047
        have hw : |(204447549/400000000 : ℝ)|=(204447549/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s1_1 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335024513/625000000 : ℝ)*x 0 + (-432274179/2500000000 : ℝ)*x 1 + (5111188633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335024513/625000000 : ℝ)^5071 ≤ (22890011421101/50000000000000 : ℝ)^4047 := by
    have hnat : (335024513 : ℕ)^5071*50000000000000^4047 ≤ 22890011421101^4047*625000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335024513 625000000 22890011421101 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432274179/2500000000 : ℝ)^5071 ≤ (11090906321867/100000000000000 : ℝ)^4047 := by
    have hnat : (432274179 : ℕ)^5071*100000000000000^4047 ≤ 11090906321867^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432274179 2500000000 11090906321867 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5111188633/10000000000 : ℝ)^5071 ≤ (43129070825821/100000000000000 : ℝ)^4047 := by
    have hnat : (5111188633 : ℕ)^5071*100000000000000^4047 ≤ 43129070825821^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5111188633 10000000000 43129070825821 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335024513/625000000 : ℝ), (-432274179/2500000000 : ℝ), (5111188633/10000000000 : ℝ)] ![(22890011421101/50000000000000 : ℝ), (11090906321867/100000000000000 : ℝ), (43129070825821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335024513/625000000 : ℝ)|^5071 ≤ (22890011421101/50000000000000 : ℝ)^4047
        have hw : |(335024513/625000000 : ℝ)|=(335024513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-432274179/2500000000 : ℝ)|^5071 ≤ (11090906321867/100000000000000 : ℝ)^4047
        have hw : |(-432274179/2500000000 : ℝ)|=(432274179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5111188633/10000000000 : ℝ)|^5071 ≤ (43129070825821/100000000000000 : ℝ)^4047
        have hw : |(5111188633/10000000000 : ℝ)|=(5111188633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s1_2 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093903/3906250 : ℝ)*x 0 + (2555594559/5000000000 : ℝ)*x 1 + (-86454839/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093903/3906250 : ℝ)^5071 ≤ (45780017191873/100000000000000 : ℝ)^4047 := by
    have hnat : (2093903 : ℕ)^5071*100000000000000^4047 ≤ 45780017191873^4047*3906250^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093903 3906250 45780017191873 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2555594559/5000000000 : ℝ)^5071 ≤ (5391134494231/12500000000000 : ℝ)^4047 := by
    have hnat : (2555594559 : ℕ)^5071*12500000000000^4047 ≤ 5391134494231^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2555594559 5000000000 5391134494231 12500000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86454839/500000000 : ℝ)^5071 ≤ (2772726709063/25000000000000 : ℝ)^4047 := by
    have hnat : (86454839 : ℕ)^5071*25000000000000^4047 ≤ 2772726709063^4047*500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86454839 500000000 2772726709063 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093903/3906250 : ℝ), (2555594559/5000000000 : ℝ), (-86454839/500000000 : ℝ)] ![(45780017191873/100000000000000 : ℝ), (5391134494231/12500000000000 : ℝ), (2772726709063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093903/3906250 : ℝ)|^5071 ≤ (45780017191873/100000000000000 : ℝ)^4047
        have hw : |(2093903/3906250 : ℝ)|=(2093903/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2555594559/5000000000 : ℝ)|^5071 ≤ (5391134494231/12500000000000 : ℝ)^4047
        have hw : |(2555594559/5000000000 : ℝ)|=(2555594559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86454839/500000000 : ℝ)|^5071 ≤ (2772726709063/25000000000000 : ℝ)^4047
        have hw : |(-86454839/500000000 : ℝ)|=(86454839/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s1_3 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2069291301/5000000000 : ℝ)*x 0 + (3614867673/10000000000 : ℝ)*x 1 + (4711994511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069291301/5000000000 : ℝ)^5071 ≤ (33105852059141/100000000000000 : ℝ)^4047 := by
    have hnat : (2069291301 : ℕ)^5071*100000000000000^4047 ≤ 33105852059141^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069291301 5000000000 33105852059141 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3614867673/10000000000 : ℝ)^5071 ≤ (27943312013/100000000000 : ℝ)^4047 := by
    have hnat : (3614867673 : ℕ)^5071*100000000000^4047 ≤ 27943312013^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3614867673 10000000000 27943312013 100000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4711994511/10000000000 : ℝ)^5071 ≤ (9737708979027/25000000000000 : ℝ)^4047 := by
    have hnat : (4711994511 : ℕ)^5071*25000000000000^4047 ≤ 9737708979027^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4711994511 10000000000 9737708979027 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2069291301/5000000000 : ℝ), (3614867673/10000000000 : ℝ), (4711994511/10000000000 : ℝ)] ![(33105852059141/100000000000000 : ℝ), (27943312013/100000000000 : ℝ), (9737708979027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2069291301/5000000000 : ℝ)|^5071 ≤ (33105852059141/100000000000000 : ℝ)^4047
        have hw : |(2069291301/5000000000 : ℝ)|=(2069291301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3614867673/10000000000 : ℝ)|^5071 ≤ (27943312013/100000000000 : ℝ)^4047
        have hw : |(3614867673/10000000000 : ℝ)|=(3614867673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4711994511/10000000000 : ℝ)|^5071 ≤ (9737708979027/25000000000000 : ℝ)^4047
        have hw : |(4711994511/10000000000 : ℝ)|=(4711994511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s1_4 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-379403663/2500000000 : ℝ)*x 0 + (5116163349/10000000000 : ℝ)*x 1 + (2755619833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (379403663/2500000000 : ℝ)^5071 ≤ (9418317328057/100000000000000 : ℝ)^4047 := by
    have hnat : (379403663 : ℕ)^5071*100000000000000^4047 ≤ 9418317328057^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379403663 2500000000 9418317328057 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5116163349/10000000000 : ℝ)^5071 ≤ (43181676228817/100000000000000 : ℝ)^4047 := by
    have hnat : (5116163349 : ℕ)^5071*100000000000000^4047 ≤ 43181676228817^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5116163349 10000000000 43181676228817 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755619833/5000000000 : ℝ)^5071 ≤ (47400006441883/100000000000000 : ℝ)^4047 := by
    have hnat : (2755619833 : ℕ)^5071*100000000000000^4047 ≤ 47400006441883^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755619833 5000000000 47400006441883 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-379403663/2500000000 : ℝ), (5116163349/10000000000 : ℝ), (2755619833/5000000000 : ℝ)] ![(9418317328057/100000000000000 : ℝ), (43181676228817/100000000000000 : ℝ), (47400006441883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-379403663/2500000000 : ℝ)|^5071 ≤ (9418317328057/100000000000000 : ℝ)^4047
        have hw : |(-379403663/2500000000 : ℝ)|=(379403663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5116163349/10000000000 : ℝ)|^5071 ≤ (43181676228817/100000000000000 : ℝ)^4047
        have hw : |(5116163349/10000000000 : ℝ)|=(5116163349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755619833/5000000000 : ℝ)|^5071 ≤ (47400006441883/100000000000000 : ℝ)^4047
        have hw : |(2755619833/5000000000 : ℝ)|=(2755619833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s1_5 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656513653/1250000000 : ℝ)*x 0 + (-1329046741/10000000000 : ℝ)*x 1 + (5511240321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656513653/1250000000 : ℝ)^5071 ≤ (44624221779173/100000000000000 : ℝ)^4047 := by
    have hnat : (656513653 : ℕ)^5071*100000000000000^4047 ≤ 44624221779173^4047*1250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656513653 1250000000 44624221779173 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1329046741/10000000000 : ℝ)^5071 ≤ (498485293933/6250000000000 : ℝ)^4047 := by
    have hnat : (1329046741 : ℕ)^5071*6250000000000^4047 ≤ 498485293933^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1329046741 10000000000 498485293933 6250000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5511240321/10000000000 : ℝ)^5071 ≤ (23700006750341/50000000000000 : ℝ)^4047 := by
    have hnat : (5511240321 : ℕ)^5071*50000000000000^4047 ≤ 23700006750341^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511240321 10000000000 23700006750341 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656513653/1250000000 : ℝ), (-1329046741/10000000000 : ℝ), (5511240321/10000000000 : ℝ)] ![(44624221779173/100000000000000 : ℝ), (498485293933/6250000000000 : ℝ), (23700006750341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656513653/1250000000 : ℝ)|^5071 ≤ (44624221779173/100000000000000 : ℝ)^4047
        have hw : |(656513653/1250000000 : ℝ)|=(656513653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1329046741/10000000000 : ℝ)|^5071 ≤ (498485293933/6250000000000 : ℝ)^4047
        have hw : |(-1329046741/10000000000 : ℝ)|=(1329046741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5511240321/10000000000 : ℝ)|^5071 ≤ (23700006750341/50000000000000 : ℝ)^4047
        have hw : |(5511240321/10000000000 : ℝ)|=(5511240321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s1_6 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131302743/250000000 : ℝ)*x 0 + (5511240189/10000000000 : ℝ)*x 1 + (-1329046227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131302743/250000000 : ℝ)^5071 ≤ (44624227059721/100000000000000 : ℝ)^4047 := by
    have hnat : (131302743 : ℕ)^5071*100000000000000^4047 ≤ 44624227059721^4047*250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131302743 250000000 44624227059721 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5511240189/10000000000 : ℝ)^5071 ≤ (9480002415629/20000000000000 : ℝ)^4047 := by
    have hnat : (5511240189 : ℕ)^5071*20000000000000^4047 ≤ 9480002415629^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511240189 10000000000 9480002415629 20000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1329046227/10000000000 : ℝ)^5071 ≤ (3987880418937/50000000000000 : ℝ)^4047 := by
    have hnat : (1329046227 : ℕ)^5071*50000000000000^4047 ≤ 3987880418937^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1329046227 10000000000 3987880418937 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131302743/250000000 : ℝ), (5511240189/10000000000 : ℝ), (-1329046227/10000000000 : ℝ)] ![(44624227059721/100000000000000 : ℝ), (9480002415629/20000000000000 : ℝ), (3987880418937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131302743/250000000 : ℝ)|^5071 ≤ (44624227059721/100000000000000 : ℝ)^4047
        have hw : |(131302743/250000000 : ℝ)|=(131302743/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5511240189/10000000000 : ℝ)|^5071 ≤ (9480002415629/20000000000000 : ℝ)^4047
        have hw : |(5511240189/10000000000 : ℝ)|=(5511240189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1329046227/10000000000 : ℝ)|^5071 ≤ (3987880418937/50000000000000 : ℝ)^4047
        have hw : |(-1329046227/10000000000 : ℝ)|=(1329046227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s1_7 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4139254073/10000000000 : ℝ)*x 0 + (4698520731/10000000000 : ℝ)*x 1 + (3628569429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4139254073/10000000000 : ℝ)^5071 ≤ (33112582596253/100000000000000 : ℝ)^4047 := by
    have hnat : (4139254073 : ℕ)^5071*100000000000000^4047 ≤ 33112582596253^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139254073 10000000000 33112582596253 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4698520731/10000000000 : ℝ)^5071 ≤ (19405663074543/50000000000000 : ℝ)^4047 := by
    have hnat : (4698520731 : ℕ)^5071*50000000000000^4047 ≤ 19405663074543^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4698520731 10000000000 19405663074543 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3628569429/10000000000 : ℝ)^5071 ≤ (14038045618333/50000000000000 : ℝ)^4047 := by
    have hnat : (3628569429 : ℕ)^5071*50000000000000^4047 ≤ 14038045618333^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3628569429 10000000000 14038045618333 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4139254073/10000000000 : ℝ), (4698520731/10000000000 : ℝ), (3628569429/10000000000 : ℝ)] ![(33112582596253/100000000000000 : ℝ), (19405663074543/50000000000000 : ℝ), (14038045618333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4139254073/10000000000 : ℝ)|^5071 ≤ (33112582596253/100000000000000 : ℝ)^4047
        have hw : |(4139254073/10000000000 : ℝ)|=(4139254073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4698520731/10000000000 : ℝ)|^5071 ≤ (19405663074543/50000000000000 : ℝ)^4047
        have hw : |(4698520731/10000000000 : ℝ)|=(4698520731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3628569429/10000000000 : ℝ)|^5071 ≤ (14038045618333/50000000000000 : ℝ)^4047
        have hw : |(3628569429/10000000000 : ℝ)|=(3628569429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1681_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (641/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9249/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17861/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (641/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (641/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (641/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (641/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (641/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (641/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (641/12500 : ℝ) ^ (5063/1024 : ℝ) ≤ (20917974109413/50000000000000000000 : ℝ) := by
    have hpowers : (641/12500 : ℝ)^5063 ≤ (20917974109413/50000000000000000000 : ℝ)^1024 := by
      have hnat : (641 : ℕ)^5063*50000000000000000000^1024 ≤ 20917974109413^1024*12500^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        641 12500 20917974109413 50000000000000000000 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (641/12500 : ℝ)) (X := (20917974109413/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22987/100000 : ℝ) ^ (5063/1024 : ℝ) ≤ (69655268160157237/100000000000000000000 : ℝ) := by
    have hpowers : (22987/100000 : ℝ)^5063 ≤ (69655268160157237/100000000000000000000 : ℝ)^1024 := by
      have hnat : (22987 : ℕ)^5063*100000000000000000000^1024 ≤ 69655268160157237^1024*100000^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22987 100000 69655268160157237 100000000000000000000 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22987/100000 : ℝ)) (X := (69655268160157237/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000020917974109413/25000000000000000000 : ℝ) ≤ (400000067691087/400000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (25000020917974109413/25000000000000000000 : ℝ)^1024 ≤ (400000067691087/400000000000000 : ℝ)^5063 := by
      have hnat : (25000020917974109413 : ℕ)^1024*400000000000000^5063 ≤ 400000067691087^5063*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000020917974109413 25000000000000000000 400000067691087 400000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000067691087/400000000000000 : ℝ)) (X := (25000020917974109413/25000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100069697104108376063/100000000000000000000 : ℝ) ≤ (10001409243567207/10000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (100069697104108376063/100000000000000000000 : ℝ)^1024 ≤ (10001409243567207/10000000000000000 : ℝ)^5063 := by
      have hnat : (100069697104108376063 : ℕ)^1024*10000000000000000^5063 ≤ 10001409243567207^5063*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100069697104108376063 100000000000000000000 10001409243567207 10000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001409243567207/10000000000000000 : ℝ)) (X := (100069697104108376063/100000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50069655268160157237/50000000000000000000 : ℝ) ≤ (10002816794857239/10000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (50069655268160157237/50000000000000000000 : ℝ)^1024 ≤ (10002816794857239/10000000000000000 : ℝ)^5063 := by
      have hnat : (50069655268160157237 : ℕ)^1024*10000000000000000^5063 ≤ 10002816794857239^5063*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50069655268160157237 50000000000000000000 10002816794857239 10000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002816794857239/10000000000000000 : ℝ)) (X := (50069655268160157237/50000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20917974109413/50000000000000000000 : ℝ) ≤ ((59525198125449166711/59530000000000000000 : ℝ)+2*(29323985209/37206250000000 : ℝ)*(641/12500 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (59525198125449166711/59530000000000000000 : ℝ)+2*(29323985209/37206250000000 : ℝ)*(641/12500 : ℝ)=(400000067691087/400000000000000 : ℝ) by norm_num, show 1+2*(20917974109413/50000000000000000000 : ℝ)=(25000020917974109413/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(69655268160157237/100000000000000000000 : ℝ)+(20917974109413/50000000000000000000 : ℝ) ≤ ((59525198125449166711/59530000000000000000 : ℝ)+(29323985209/37206250000000 : ℝ)*((22987/100000 : ℝ)+(641/12500 : ℝ)))^(5063/1024 : ℝ) := by
    rw [show (59525198125449166711/59530000000000000000 : ℝ)+(29323985209/37206250000000 : ℝ)*((22987/100000 : ℝ)+(641/12500 : ℝ))=(10001409243567207/10000000000000000 : ℝ) by norm_num, show 1+(69655268160157237/100000000000000000000 : ℝ)+(20917974109413/50000000000000000000 : ℝ)=(100069697104108376063/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(69655268160157237/100000000000000000000 : ℝ) ≤ ((59525198125449166711/59530000000000000000 : ℝ)+2*(29323985209/37206250000000 : ℝ)*(22987/100000 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (59525198125449166711/59530000000000000000 : ℝ)+2*(29323985209/37206250000000 : ℝ)*(22987/100000 : ℝ)=(10002816794857239/10000000000000000 : ℝ) by norm_num, show 1+2*(69655268160157237/100000000000000000000 : ℝ)=(50069655268160157237/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59525198125449166711/59530000000000000000 : ℝ)*(X 1 0+X 2 0)+(29323985209/37206250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (641/12500 : ℝ)) (hi := (22987/100000 : ℝ)) (c := (59525198125449166711/59530000000000000000 : ℝ)) (alpha := (29323985209/37206250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59525198125449166711/59530000000000000000 : ℝ)*(X 0 1+X 2 1)+(29323985209/37206250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (641/12500 : ℝ)) (hi := (22987/100000 : ℝ)) (c := (59525198125449166711/59530000000000000000 : ℝ)) (alpha := (29323985209/37206250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59525198125449166711/59530000000000000000 : ℝ)*(X 0 2+X 1 2)+(29323985209/37206250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (641/12500 : ℝ)) (hi := (22987/100000 : ℝ)) (c := (59525198125449166711/59530000000000000000 : ℝ)) (alpha := (29323985209/37206250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-303473321/2000000000 : ℝ)*X 0 0+(5516299329/10000000000 : ℝ)*X 0 1+(204447549/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335024513/625000000 : ℝ)*X 1 0+(-432274179/2500000000 : ℝ)*X 1 1+(5111188633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2093903/3906250 : ℝ)*X 2 0+(2555594559/5000000000 : ℝ)*X 2 1+(-86454839/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2069291301/5000000000 : ℝ)*X 0 0+(3614867673/10000000000 : ℝ)*X 0 1+(4711994511/10000000000 : ℝ)*X 0 2+(2069291301/5000000000 : ℝ)*X 1 0+(3614867673/10000000000 : ℝ)*X 1 1+(4711994511/10000000000 : ℝ)*X 1 2+(2069291301/5000000000 : ℝ)*X 2 0+(3614867673/10000000000 : ℝ)*X 2 1+(4711994511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-379403663/2500000000 : ℝ)*X 0 0+(5116163349/10000000000 : ℝ)*X 0 1+(2755619833/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((656513653/1250000000 : ℝ)*X 1 0+(-1329046741/10000000000 : ℝ)*X 1 1+(5511240321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((131302743/250000000 : ℝ)*X 2 0+(5511240189/10000000000 : ℝ)*X 2 1+(-1329046227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4139254073/10000000000 : ℝ)*X 0 0+(4698520731/10000000000 : ℝ)*X 0 1+(3628569429/10000000000 : ℝ)*X 0 2+(4139254073/10000000000 : ℝ)*X 1 0+(4698520731/10000000000 : ℝ)*X 1 1+(3628569429/10000000000 : ℝ)*X 1 2+(4139254073/10000000000 : ℝ)*X 2 0+(4698520731/10000000000 : ℝ)*X 2 1+(3628569429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89853527593285121763969/7441250000000000000000000000 : ℝ) := by norm_num
    linear_combination (460317167/25000000000000 : ℝ)*(base19) + (798305661/50000000000000 : ℝ)*(base23) + (280717643/100000000000000 : ℝ)*(upper3) + (809587/100000000000000 : ℝ)*(upper4) + (205662269/100000000000000 : ℝ)*(upper5) + (422497059004063/25000000000000 : ℝ)*(major0) + (422497059004063/25000000000000 : ℝ)*(major1) + (422497059004063/25000000000000 : ℝ)*(major2) + (123423903860853/5000000000000 : ℝ)*(sp0) + (154280697024517/6250000000000 : ℝ)*(sp1) + (1234245698524809/50000000000000 : ℝ)*(sp2) + (911477208774571/100000000000000 : ℝ)*(sp3) + (372911097/2500000000000 : ℝ)*(sp4) + (733386881/12500000000000 : ℝ)*(sp7) + (911483075869619/100000000000000 : ℝ)*(f.failure) + (123424649683047/5000000000000 : ℝ)*(f.sum) + (6121531292699/14882500000000000000000000000 : ℝ)*base65 + (1925443788294796793/1488250000000000000000000000000000 : ℝ)*base67 + (5485252025471703207/1488250000000000000000000000000000 : ℝ)*base70 + (2252009606239046793/1488250000000000000000000000000000 : ℝ)*base71 + (6883236382153/29765000000000000000000000000 : ℝ)*base73 + (2262969913218703207/1488250000000000000000000000000000 : ℝ)*base76 + (2936270490208953207/1488250000000000000000000000000000 : ℝ)*base78 + (1492437355546796793/1488250000000000000000000000000000 : ℝ)*base79 + (65911021350057/29765000000000000000000000000 : ℝ)*base82 + (3992039/10000000000000000000000 : ℝ)*base90 + (3992039/10000000000000000000000 : ℝ)*base92 + (3992039/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32321341201854349603386103479/2976500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101852127/10000000000000 : ℝ)*(base19) + (348308353/25000000000000 : ℝ)*(base23) + (18010353/50000000000000 : ℝ)*(upper2) + (165484339/50000000000000 : ℝ)*(upper3) + (78149599/20000000000000 : ℝ)*(upper5) + (1732890085694763/100000000000000 : ℝ)*(major0) + (1732890085694763/100000000000000 : ℝ)*(major1) + (1732890085694763/100000000000000 : ℝ)*(major2) + (1459870793/20000000000000 : ℝ)*(sp1) + (10553597501/100000000000000 : ℝ)*(sp2) + (632789481894069/25000000000000 : ℝ)*(sp4) + (2531149609701041/100000000000000 : ℝ)*(sp5) + (2531145980745363/100000000000000 : ℝ)*(sp6) + (934621881851869/100000000000000 : ℝ)*(sp7) + (934621881851869/100000000000000 : ℝ)*(f.failure) + (632789481894069/25000000000000 : ℝ)*(f.sum) + (89717110991447/29765000000000000000000000000 : ℝ)*base65 + (15196395246945165507/5953000000000000000000000000000000 : ℝ)*base68 + (23204799784407165507/5953000000000000000000000000000000 : ℝ)*base70 + (5999768579620834493/5953000000000000000000000000000000 : ℝ)*base71 + (53417191395899/14882500000000000000000000000 : ℝ)*base74 + (2575215185477165507/5953000000000000000000000000000000 : ℝ)*base76 + (20596446381012834493/5953000000000000000000000000000000 : ℝ)*base77 + (2880110921098165507/5953000000000000000000000000000000 : ℝ)*base80 + (5744441709207/7441250000000000000000000000 : ℝ)*base82 + (32029289/10000000000000000000000 : ℝ)*base90 + (32029289/10000000000000000000000 : ℝ)*base92 + (32029289/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1681_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (641/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17861/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1681_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1681_s2_0 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-152379099/1000000000 : ℝ)*x 0 + (5490869961/10000000000 : ℝ)*x 1 + (5132360157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (152379099/1000000000 : ℝ)^5071 ≤ (37865484007/400000000000 : ℝ)^4047 := by
    have hnat : (152379099 : ℕ)^5071*400000000000^4047 ≤ 37865484007^4047*1000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152379099 1000000000 37865484007 400000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490869961/10000000000 : ℝ)^5071 ≤ (47180589105301/100000000000000 : ℝ)^4047 := by
    have hnat : (5490869961 : ℕ)^5071*100000000000000^4047 ≤ 47180589105301^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490869961 10000000000 47180589105301 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5132360157/10000000000 : ℝ)^5071 ≤ (10838259969881/25000000000000 : ℝ)^4047 := by
    have hnat : (5132360157 : ℕ)^5071*25000000000000^4047 ≤ 10838259969881^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132360157 10000000000 10838259969881 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-152379099/1000000000 : ℝ), (5490869961/10000000000 : ℝ), (5132360157/10000000000 : ℝ)] ![(37865484007/400000000000 : ℝ), (47180589105301/100000000000000 : ℝ), (10838259969881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-152379099/1000000000 : ℝ)|^5071 ≤ (37865484007/400000000000 : ℝ)^4047
        have hw : |(-152379099/1000000000 : ℝ)|=(152379099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490869961/10000000000 : ℝ)|^5071 ≤ (47180589105301/100000000000000 : ℝ)^4047
        have hw : |(5490869961/10000000000 : ℝ)|=(5490869961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5132360157/10000000000 : ℝ)|^5071 ≤ (10838259969881/25000000000000 : ℝ)^4047
        have hw : |(5132360157/10000000000 : ℝ)|=(5132360157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s2_1 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535361159/1000000000 : ℝ)*x 0 + (-855115289/5000000000 : ℝ)*x 1 + (513236049/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535361159/1000000000 : ℝ)^5071 ≤ (45707472478613/100000000000000 : ℝ)^4047 := by
    have hnat : (535361159 : ℕ)^5071*100000000000000^4047 ≤ 45707472478613^4047*1000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535361159 1000000000 45707472478613 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (855115289/5000000000 : ℝ)^5071 ≤ (10939484098997/100000000000000 : ℝ)^4047 := by
    have hnat : (855115289 : ℕ)^5071*100000000000000^4047 ≤ 10939484098997^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855115289 5000000000 10939484098997 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513236049/1000000000 : ℝ)^5071 ≤ (43353043404101/100000000000000 : ℝ)^4047 := by
    have hnat : (513236049 : ℕ)^5071*100000000000000^4047 ≤ 43353043404101^4047*1000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513236049 1000000000 43353043404101 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535361159/1000000000 : ℝ), (-855115289/5000000000 : ℝ), (513236049/1000000000 : ℝ)] ![(45707472478613/100000000000000 : ℝ), (10939484098997/100000000000000 : ℝ), (43353043404101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535361159/1000000000 : ℝ)|^5071 ≤ (45707472478613/100000000000000 : ℝ)^4047
        have hw : |(535361159/1000000000 : ℝ)|=(535361159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-855115289/5000000000 : ℝ)|^5071 ≤ (10939484098997/100000000000000 : ℝ)^4047
        have hw : |(-855115289/5000000000 : ℝ)|=(855115289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513236049/1000000000 : ℝ)|^5071 ≤ (43353043404101/100000000000000 : ℝ)^4047
        have hw : |(513236049/1000000000 : ℝ)|=(513236049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s2_2 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167300381/312500000 : ℝ)*x 0 + (1283089939/2500000000 : ℝ)*x 1 + (-213778843/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167300381/312500000 : ℝ)^5071 ≤ (22853739459391/50000000000000 : ℝ)^4047 := by
    have hnat : (167300381 : ℕ)^5071*50000000000000^4047 ≤ 22853739459391^4047*312500000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167300381 312500000 22853739459391 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283089939/2500000000 : ℝ)^5071 ≤ (43353035635213/100000000000000 : ℝ)^4047 := by
    have hnat : (1283089939 : ℕ)^5071*100000000000000^4047 ≤ 43353035635213^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283089939 2500000000 43353035635213 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213778843/1250000000 : ℝ)^5071 ≤ (2734871357371/25000000000000 : ℝ)^4047 := by
    have hnat : (213778843 : ℕ)^5071*25000000000000^4047 ≤ 2734871357371^4047*1250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213778843 1250000000 2734871357371 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167300381/312500000 : ℝ), (1283089939/2500000000 : ℝ), (-213778843/1250000000 : ℝ)] ![(22853739459391/50000000000000 : ℝ), (43353035635213/100000000000000 : ℝ), (2734871357371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167300381/312500000 : ℝ)|^5071 ≤ (22853739459391/50000000000000 : ℝ)^4047
        have hw : |(167300381/312500000 : ℝ)|=(167300381/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283089939/2500000000 : ℝ)|^5071 ≤ (43353035635213/100000000000000 : ℝ)^4047
        have hw : |(1283089939/2500000000 : ℝ)|=(1283089939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213778843/1250000000 : ℝ)|^5071 ≤ (2734871357371/25000000000000 : ℝ)^4047
        have hw : |(-213778843/1250000000 : ℝ)|=(213778843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s2_3 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4143504557/10000000000 : ℝ)*x 0 + (3677500647/10000000000 : ℝ)*x 1 + (4648423933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4143504557/10000000000 : ℝ)^5071 ≤ (8288798507917/25000000000000 : ℝ)^4047 := by
    have hnat : (4143504557 : ℕ)^5071*25000000000000^4047 ≤ 8288798507917^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143504557 10000000000 8288798507917 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3677500647/10000000000 : ℝ)^5071 ≤ (28551301115767/100000000000000 : ℝ)^4047 := by
    have hnat : (3677500647 : ℕ)^5071*100000000000000^4047 ≤ 28551301115767^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3677500647 10000000000 28551301115767 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4648423933/10000000000 : ℝ)^5071 ≤ (19146752417993/50000000000000 : ℝ)^4047 := by
    have hnat : (4648423933 : ℕ)^5071*50000000000000^4047 ≤ 19146752417993^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4648423933 10000000000 19146752417993 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4143504557/10000000000 : ℝ), (3677500647/10000000000 : ℝ), (4648423933/10000000000 : ℝ)] ![(8288798507917/25000000000000 : ℝ), (28551301115767/100000000000000 : ℝ), (19146752417993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4143504557/10000000000 : ℝ)|^5071 ≤ (8288798507917/25000000000000 : ℝ)^4047
        have hw : |(4143504557/10000000000 : ℝ)|=(4143504557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3677500647/10000000000 : ℝ)|^5071 ≤ (28551301115767/100000000000000 : ℝ)^4047
        have hw : |(3677500647/10000000000 : ℝ)|=(3677500647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4648423933/10000000000 : ℝ)|^5071 ≤ (19146752417993/50000000000000 : ℝ)^4047
        have hw : |(4648423933/10000000000 : ℝ)|=(4648423933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s2_4 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1523962669/10000000000 : ℝ)*x 0 + (5136260371/10000000000 : ℝ)*x 1 + (68586387/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1523962669/10000000000 : ℝ)^5071 ≤ (9467707418441/100000000000000 : ℝ)^4047 := by
    have hnat : (1523962669 : ℕ)^5071*100000000000000^4047 ≤ 9467707418441^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523962669 10000000000 9467707418441 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136260371/10000000000 : ℝ)^5071 ≤ (8678864989747/20000000000000 : ℝ)^4047 := by
    have hnat : (5136260371 : ℕ)^5071*20000000000000^4047 ≤ 8678864989747^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136260371 10000000000 8678864989747 20000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68586387/125000000 : ℝ)^5071 ≤ (2356898380933/5000000000000 : ℝ)^4047 := by
    have hnat : (68586387 : ℕ)^5071*5000000000000^4047 ≤ 2356898380933^4047*125000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68586387 125000000 2356898380933 5000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1523962669/10000000000 : ℝ), (5136260371/10000000000 : ℝ), (68586387/125000000 : ℝ)] ![(9467707418441/100000000000000 : ℝ), (8678864989747/20000000000000 : ℝ), (2356898380933/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1523962669/10000000000 : ℝ)|^5071 ≤ (9467707418441/100000000000000 : ℝ)^4047
        have hw : |(-1523962669/10000000000 : ℝ)|=(1523962669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136260371/10000000000 : ℝ)|^5071 ≤ (8678864989747/20000000000000 : ℝ)^4047
        have hw : |(5136260371/10000000000 : ℝ)|=(5136260371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68586387/125000000 : ℝ)|^5071 ≤ (2356898380933/5000000000000 : ℝ)^4047
        have hw : |(68586387/125000000 : ℝ)|=(68586387/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s2_5 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657232953/1250000000 : ℝ)*x 0 + (-169459983/1250000000 : ℝ)*x 1 + (685863869/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657232953/1250000000 : ℝ)^5071 ≤ (893709862833/2000000000000 : ℝ)^4047 := by
    have hnat : (657232953 : ℕ)^5071*2000000000000^4047 ≤ 893709862833^4047*1250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657232953 1250000000 893709862833 2000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169459983/1250000000 : ℝ)^5071 ≤ (1635307862773/20000000000000 : ℝ)^4047 := by
    have hnat : (169459983 : ℕ)^5071*20000000000000^4047 ≤ 1635307862773^4047*1250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169459983 1250000000 1635307862773 20000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685863869/1250000000 : ℝ)^5071 ≤ (23568983766271/50000000000000 : ℝ)^4047 := by
    have hnat : (685863869 : ℕ)^5071*50000000000000^4047 ≤ 23568983766271^4047*1250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685863869 1250000000 23568983766271 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657232953/1250000000 : ℝ), (-169459983/1250000000 : ℝ), (685863869/1250000000 : ℝ)] ![(893709862833/2000000000000 : ℝ), (1635307862773/20000000000000 : ℝ), (23568983766271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657232953/1250000000 : ℝ)|^5071 ≤ (893709862833/2000000000000 : ℝ)^4047
        have hw : |(657232953/1250000000 : ℝ)|=(657232953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169459983/1250000000 : ℝ)|^5071 ≤ (1635307862773/20000000000000 : ℝ)^4047
        have hw : |(-169459983/1250000000 : ℝ)|=(169459983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685863869/1250000000 : ℝ)|^5071 ≤ (23568983766271/50000000000000 : ℝ)^4047
        have hw : |(685863869/1250000000 : ℝ)|=(685863869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s2_6 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628931813/5000000000 : ℝ)*x 0 + (685863871/1250000000 : ℝ)*x 1 + (-677839919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628931813/5000000000 : ℝ)^5071 ≤ (11171373290737/25000000000000 : ℝ)^4047 := by
    have hnat : (2628931813 : ℕ)^5071*25000000000000^4047 ≤ 11171373290737^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628931813 5000000000 11171373290737 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685863871/1250000000 : ℝ)^5071 ≤ (47137967704777/100000000000000 : ℝ)^4047 := by
    have hnat : (685863871 : ℕ)^5071*100000000000000^4047 ≤ 47137967704777^4047*1250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685863871 1250000000 47137967704777 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677839919/5000000000 : ℝ)^5071 ≤ (8176539117373/100000000000000 : ℝ)^4047 := by
    have hnat : (677839919 : ℕ)^5071*100000000000000^4047 ≤ 8176539117373^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677839919 5000000000 8176539117373 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628931813/5000000000 : ℝ), (685863871/1250000000 : ℝ), (-677839919/5000000000 : ℝ)] ![(11171373290737/25000000000000 : ℝ), (47137967704777/100000000000000 : ℝ), (8176539117373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628931813/5000000000 : ℝ)|^5071 ≤ (11171373290737/25000000000000 : ℝ)^4047
        have hw : |(2628931813/5000000000 : ℝ)|=(2628931813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685863871/1250000000 : ℝ)|^5071 ≤ (47137967704777/100000000000000 : ℝ)^4047
        have hw : |(685863871/1250000000 : ℝ)|=(685863871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-677839919/5000000000 : ℝ)|^5071 ≤ (8176539117373/100000000000000 : ℝ)^4047
        have hw : |(-677839919/5000000000 : ℝ)|=(677839919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s2_7 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4143969317/10000000000 : ℝ)*x 0 + (2318930303/5000000000 : ℝ)*x 1 + (3688222947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4143969317/10000000000 : ℝ)^5071 ≤ (8289963489537/25000000000000 : ℝ)^4047 := by
    have hnat : (4143969317 : ℕ)^5071*25000000000000^4047 ≤ 8289963489537^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143969317 10000000000 8289963489537 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2318930303/5000000000 : ℝ)^5071 ≤ (190922487693/500000000000 : ℝ)^4047 := by
    have hnat : (2318930303 : ℕ)^5071*500000000000^4047 ≤ 190922487693^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2318930303 5000000000 190922487693 500000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3688222947/10000000000 : ℝ)^5071 ≤ (14327824249069/50000000000000 : ℝ)^4047 := by
    have hnat : (3688222947 : ℕ)^5071*50000000000000^4047 ≤ 14327824249069^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688222947 10000000000 14327824249069 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4143969317/10000000000 : ℝ), (2318930303/5000000000 : ℝ), (3688222947/10000000000 : ℝ)] ![(8289963489537/25000000000000 : ℝ), (190922487693/500000000000 : ℝ), (14327824249069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4143969317/10000000000 : ℝ)|^5071 ≤ (8289963489537/25000000000000 : ℝ)^4047
        have hw : |(4143969317/10000000000 : ℝ)|=(4143969317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2318930303/5000000000 : ℝ)|^5071 ≤ (190922487693/500000000000 : ℝ)^4047
        have hw : |(2318930303/5000000000 : ℝ)|=(2318930303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3688222947/10000000000 : ℝ)|^5071 ≤ (14327824249069/50000000000000 : ℝ)^4047
        have hw : |(3688222947/10000000000 : ℝ)|=(3688222947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1681_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17861/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (971/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1733/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17861/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17861/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17861/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17861/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17861/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17861/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9249/100000 : ℝ) ^ (5063/1024 : ℝ) ≤ (30909021267873/4000000000000000000 : ℝ) := by
    have hpowers : (9249/100000 : ℝ)^5063 ≤ (30909021267873/4000000000000000000 : ℝ)^1024 := by
      have hnat : (9249 : ℕ)^5063*4000000000000000000^1024 ≤ 30909021267873^1024*100000^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9249 100000 30909021267873 4000000000000000000 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9249/100000 : ℝ)) (X := (30909021267873/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17861/100000 : ℝ) ^ (5063/1024 : ℝ) ≤ (2500810760232841/12500000000000000000 : ℝ) := by
    have hpowers : (17861/100000 : ℝ)^5063 ≤ (2500810760232841/12500000000000000000 : ℝ)^1024 := by
      have hnat : (17861 : ℕ)^5063*12500000000000000000^1024 ≤ 2500810760232841^1024*100000^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17861 100000 2500810760232841 12500000000000000000 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17861/100000 : ℝ)) (X := (2500810760232841/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000030909021267873/2000000000000000000 : ℝ) ≤ (2000006251361381/2000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (2000030909021267873/2000000000000000000 : ℝ)^1024 ≤ (2000006251361381/2000000000000000 : ℝ)^5063 := by
      have hnat : (2000030909021267873 : ℕ)^1024*2000000000000000^5063 ≤ 2000006251361381^5063*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000030909021267873 2000000000000000000 2000006251361381 2000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000006251361381/2000000000000000 : ℝ)) (X := (2000030909021267873/2000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100020779211613559553/100000000000000000000 : ℝ) ≤ (10000420228112513/10000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (100020779211613559553/100000000000000000000 : ℝ)^1024 ≤ (10000420228112513/10000000000000000 : ℝ)^5063 := by
      have hnat : (100020779211613559553 : ℕ)^1024*10000000000000000^5063 ≤ 10000420228112513^5063*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100020779211613559553 100000000000000000000 10000420228112513 10000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000420228112513/10000000000000000 : ℝ)) (X := (100020779211613559553/100000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252500810760232841/6250000000000000000 : ℝ) ≤ (10000809199418121/10000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (6252500810760232841/6250000000000000000 : ℝ)^1024 ≤ (10000809199418121/10000000000000000 : ℝ)^5063 := by
      have hnat : (6252500810760232841 : ℕ)^1024*10000000000000000^5063 ≤ 10000809199418121^5063*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252500810760232841 6250000000000000000 10000809199418121 10000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000809199418121/10000000000000000 : ℝ)) (X := (6252500810760232841/6250000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(30909021267873/4000000000000000000 : ℝ) ≤ ((21528268498102482269/21530000000000000000 : ℝ)+2*(48621413201/107650000000000 : ℝ)*(9249/100000 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (21528268498102482269/21530000000000000000 : ℝ)+2*(48621413201/107650000000000 : ℝ)*(9249/100000 : ℝ)=(2000006251361381/2000000000000000 : ℝ) by norm_num, show 1+2*(30909021267873/4000000000000000000 : ℝ)=(2000030909021267873/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2500810760232841/12500000000000000000 : ℝ)+(30909021267873/4000000000000000000 : ℝ) ≤ ((21528268498102482269/21530000000000000000 : ℝ)+(48621413201/107650000000000 : ℝ)*((17861/100000 : ℝ)+(9249/100000 : ℝ)))^(5063/1024 : ℝ) := by
    rw [show (21528268498102482269/21530000000000000000 : ℝ)+(48621413201/107650000000000 : ℝ)*((17861/100000 : ℝ)+(9249/100000 : ℝ))=(10000420228112513/10000000000000000 : ℝ) by norm_num, show 1+(2500810760232841/12500000000000000000 : ℝ)+(30909021267873/4000000000000000000 : ℝ)=(100020779211613559553/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2500810760232841/12500000000000000000 : ℝ) ≤ ((21528268498102482269/21530000000000000000 : ℝ)+2*(48621413201/107650000000000 : ℝ)*(17861/100000 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (21528268498102482269/21530000000000000000 : ℝ)+2*(48621413201/107650000000000 : ℝ)*(17861/100000 : ℝ)=(10000809199418121/10000000000000000 : ℝ) by norm_num, show 1+2*(2500810760232841/12500000000000000000 : ℝ)=(6252500810760232841/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21528268498102482269/21530000000000000000 : ℝ)*(X 1 0+X 2 0)+(48621413201/107650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (9249/100000 : ℝ)) (hi := (17861/100000 : ℝ)) (c := (21528268498102482269/21530000000000000000 : ℝ)) (alpha := (48621413201/107650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21528268498102482269/21530000000000000000 : ℝ)*(X 0 1+X 2 1)+(48621413201/107650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (9249/100000 : ℝ)) (hi := (17861/100000 : ℝ)) (c := (21528268498102482269/21530000000000000000 : ℝ)) (alpha := (48621413201/107650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21528268498102482269/21530000000000000000 : ℝ)*(X 0 2+X 1 2)+(48621413201/107650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (9249/100000 : ℝ)) (hi := (17861/100000 : ℝ)) (c := (21528268498102482269/21530000000000000000 : ℝ)) (alpha := (48621413201/107650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-152379099/1000000000 : ℝ)*X 0 0+(5490869961/10000000000 : ℝ)*X 0 1+(5132360157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535361159/1000000000 : ℝ)*X 1 0+(-855115289/5000000000 : ℝ)*X 1 1+(513236049/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167300381/312500000 : ℝ)*X 2 0+(1283089939/2500000000 : ℝ)*X 2 1+(-213778843/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4143504557/10000000000 : ℝ)*X 0 0+(3677500647/10000000000 : ℝ)*X 0 1+(4648423933/10000000000 : ℝ)*X 0 2+(4143504557/10000000000 : ℝ)*X 1 0+(3677500647/10000000000 : ℝ)*X 1 1+(4648423933/10000000000 : ℝ)*X 1 2+(4143504557/10000000000 : ℝ)*X 2 0+(3677500647/10000000000 : ℝ)*X 2 1+(4648423933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1523962669/10000000000 : ℝ)*X 0 0+(5136260371/10000000000 : ℝ)*X 0 1+(68586387/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((657232953/1250000000 : ℝ)*X 1 0+(-169459983/1250000000 : ℝ)*X 1 1+(685863869/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2628931813/5000000000 : ℝ)*X 2 0+(685863871/1250000000 : ℝ)*X 2 1+(-677839919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4143969317/10000000000 : ℝ)*X 0 0+(2318930303/5000000000 : ℝ)*X 0 1+(3688222947/10000000000 : ℝ)*X 0 2+(4143969317/10000000000 : ℝ)*X 1 0+(2318930303/5000000000 : ℝ)*X 1 1+(3688222947/10000000000 : ℝ)*X 1 2+(4143969317/10000000000 : ℝ)*X 2 0+(2318930303/5000000000 : ℝ)*X 2 1+(3688222947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75883587246199136163/26912500000000000000000000 : ℝ) := by norm_num
    linear_combination (117877067/50000000000000 : ℝ)*(base19) + (101059443/20000000000000 : ℝ)*(base23) + (31061123/100000000000000 : ℝ)*(lower2) + (87112923/100000000000000 : ℝ)*(upper3) + (7446317/100000000000000 : ℝ)*(lower4) + (23870516093037/1250000000000 : ℝ)*(major0) + (23870516093037/1250000000000 : ℝ)*(major1) + (23870516093037/1250000000000 : ℝ)*(major2) + (2789327702247809/100000000000000 : ℝ)*(sp0) + (348666358245231/12500000000000 : ℝ)*(sp1) + (174333162276173/6250000000000 : ℝ)*(sp2) + (514974479898359/50000000000000 : ℝ)*(sp3) + (1699734087/50000000000000 : ℝ)*(sp4) + (75605787/3125000000000 : ℝ)*(sp7) + (514975689590951/50000000000000 : ℝ)*(f.failure) + (2789331101715983/100000000000000 : ℝ)*(f.sum) + (714384937853/215300000000000000000000000 : ℝ)*base66 + (3916282457898453/26912500000000000000000000000000 : ℝ)*base67 + (44963980088676547/26912500000000000000000000000000 : ℝ)*base70 + (416970623985953/26912500000000000000000000000000 : ℝ)*base71 + (1010009670817/1076500000000000000000000000 : ℝ)*base74 + (273178035393185953/26912500000000000000000000000000 : ℝ)*base75 + (52110877448614047/26912500000000000000000000000000 : ℝ)*base78 + (33712845149164047/26912500000000000000000000000000 : ℝ)*base80 + (1704583323117/1076500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (101131/5000000000000000000000 : ℝ)*base90 + (101131/5000000000000000000000 : ℝ)*base92 + (101131/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5796825303626454095504672961/538250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1538224637/100000000000000 : ℝ)*(base19) + (335423851/20000000000000 : ℝ)*(base23) + (230992649/100000000000000 : ℝ)*(upper3) + (12003649/20000000000000 : ℝ)*(lower4) + (56474109/25000000000000 : ℝ)*(upper5) + (976218613205223/50000000000000 : ℝ)*(major0) + (976218613205223/50000000000000 : ℝ)*(major1) + (976218613205223/50000000000000 : ℝ)*(major2) + (3250174547/25000000000000 : ℝ)*(sp1) + (1787485309/12500000000000 : ℝ)*(sp2) + (1425920515424801/50000000000000 : ℝ)*(sp4) + (356478311490847/12500000000000 : ℝ)*(sp5) + (712956263461969/25000000000000 : ℝ)*(sp6) + (26325826574479/2500000000000 : ℝ)*(sp7) + (26325826574479/2500000000000 : ℝ)*(f.failure) + (1425920515424801/50000000000000 : ℝ)*(f.sum) + (21520644599531/5382500000000000000000000000 : ℝ)*base65 + (1838639261222709013/1076500000000000000000000000000000 : ℝ)*base68 + (3866043078279709013/1076500000000000000000000000000000 : ℝ)*base70 + (10838832356284290987/1076500000000000000000000000000000 : ℝ)*base71 + (19009245974047/2691250000000000000000000000 : ℝ)*base74 + (6902396390892290987/1076500000000000000000000000000000 : ℝ)*base75 + (2351804031699709013/1076500000000000000000000000000000 : ℝ)*base78 + (9413731271259709013/1076500000000000000000000000000000 : ℝ)*base80 + (11395165327917/2691250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (888301/250000000000000000000 : ℝ)*base89 + (888301/250000000000000000000 : ℝ)*base91 + (888301/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1681_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17861/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (971/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1733/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1681_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1681_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (971/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1733/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1681_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1681_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1681_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (971/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1733/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1681_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
