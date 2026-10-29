-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1611_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:43.087953+00:00
-- url     : https://prove2.me/submissions/cd8bcea6-2236-426d-bb08-2c6de9e7d14e

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
theorem support_rectangle_w1611_s3_0 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-170165487/1000000000 : ℝ)*x 0 + (2729848579/5000000000 : ℝ)*x 1 + (2590210837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170165487/1000000000 : ℝ)^4763 ≤ (10476838252641/100000000000000 : ℝ)^3739 := by
    have hnat : (170165487 : ℕ)^4763*100000000000000^3739 ≤ 10476838252641^3739*1000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170165487 1000000000 10476838252641 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729848579/5000000000 : ℝ)^4763 ≤ (46258005190031/100000000000000 : ℝ)^3739 := by
    have hnat : (2729848579 : ℕ)^4763*100000000000000^3739 ≤ 46258005190031^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729848579 5000000000 46258005190031 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590210837/5000000000 : ℝ)^4763 ≤ (43265156552267/100000000000000 : ℝ)^3739 := by
    have hnat : (2590210837 : ℕ)^4763*100000000000000^3739 ≤ 43265156552267^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590210837 5000000000 43265156552267 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-170165487/1000000000 : ℝ), (2729848579/5000000000 : ℝ), (2590210837/5000000000 : ℝ)] ![(10476838252641/100000000000000 : ℝ), (46258005190031/100000000000000 : ℝ), (43265156552267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-170165487/1000000000 : ℝ)|^4763 ≤ (10476838252641/100000000000000 : ℝ)^3739
        have hw : |(-170165487/1000000000 : ℝ)|=(170165487/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729848579/5000000000 : ℝ)|^4763 ≤ (46258005190031/100000000000000 : ℝ)^3739
        have hw : |(2729848579/5000000000 : ℝ)|=(2729848579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590210837/5000000000 : ℝ)|^4763 ≤ (43265156552267/100000000000000 : ℝ)^3739
        have hw : |(2590210837/5000000000 : ℝ)|=(2590210837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s3_1 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338392679/2500000000 : ℝ)*x 0 + (-369134473/2000000000 : ℝ)*x 1 + (5180421437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338392679/2500000000 : ℝ)^4763 ≤ (22557821214673/50000000000000 : ℝ)^3739 := by
    have hnat : (1338392679 : ℕ)^4763*50000000000000^3739 ≤ 22557821214673^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338392679 2500000000 22557821214673 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369134473/2000000000 : ℝ)^4763 ≤ (5809601760503/50000000000000 : ℝ)^3739 := by
    have hnat : (369134473 : ℕ)^4763*50000000000000^3739 ≤ 5809601760503^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369134473 2000000000 5809601760503 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180421437/10000000000 : ℝ)^4763 ≤ (43265154030839/100000000000000 : ℝ)^3739 := by
    have hnat : (5180421437 : ℕ)^4763*100000000000000^3739 ≤ 43265154030839^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180421437 10000000000 43265154030839 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338392679/2500000000 : ℝ), (-369134473/2000000000 : ℝ), (5180421437/10000000000 : ℝ)] ![(22557821214673/50000000000000 : ℝ), (5809601760503/50000000000000 : ℝ), (43265154030839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338392679/2500000000 : ℝ)|^4763 ≤ (22557821214673/50000000000000 : ℝ)^3739
        have hw : |(1338392679/2500000000 : ℝ)|=(1338392679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-369134473/2000000000 : ℝ)|^4763 ≤ (5809601760503/50000000000000 : ℝ)^3739
        have hw : |(-369134473/2000000000 : ℝ)|=(369134473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180421437/10000000000 : ℝ)|^4763 ≤ (43265154030839/100000000000000 : ℝ)^3739
        have hw : |(5180421437/10000000000 : ℝ)|=(5180421437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s3_2 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338392703/2500000000 : ℝ)*x 0 + (5180421233/10000000000 : ℝ)*x 1 + (-461418127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338392703/2500000000 : ℝ)^4763 ≤ (22557821729961/50000000000000 : ℝ)^3739 := by
    have hnat : (1338392703 : ℕ)^4763*50000000000000^3739 ≤ 22557821729961^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338392703 2500000000 22557821729961 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180421233/10000000000 : ℝ)^4763 ≤ (8653030372099/20000000000000 : ℝ)^3739 := by
    have hnat : (5180421233 : ℕ)^4763*20000000000000^3739 ≤ 8653030372099^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180421233 10000000000 8653030372099 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461418127/2500000000 : ℝ)^4763 ≤ (11619204667793/100000000000000 : ℝ)^3739 := by
    have hnat : (461418127 : ℕ)^4763*100000000000000^3739 ≤ 11619204667793^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461418127 2500000000 11619204667793 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338392703/2500000000 : ℝ), (5180421233/10000000000 : ℝ), (-461418127/2500000000 : ℝ)] ![(22557821729961/50000000000000 : ℝ), (8653030372099/20000000000000 : ℝ), (11619204667793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338392703/2500000000 : ℝ)|^4763 ≤ (22557821729961/50000000000000 : ℝ)^3739
        have hw : |(1338392703/2500000000 : ℝ)|=(1338392703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180421233/10000000000 : ℝ)|^4763 ≤ (8653030372099/20000000000000 : ℝ)^3739
        have hw : |(5180421233/10000000000 : ℝ)|=(5180421233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-461418127/2500000000 : ℝ)|^4763 ≤ (11619204667793/100000000000000 : ℝ)^3739
        have hw : |(-461418127/2500000000 : ℝ)|=(461418127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s3_3 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4211649161/10000000000 : ℝ)*x 0 + (387883521/1000000000 : ℝ)*x 1 + (4566014633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211649161/10000000000 : ℝ)^4763 ≤ (2077212450387/6250000000000 : ℝ)^3739 := by
    have hnat : (4211649161 : ℕ)^4763*6250000000000^3739 ≤ 2077212450387^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211649161 10000000000 2077212450387 6250000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387883521/1000000000 : ℝ)^4763 ≤ (5985341716021/20000000000000 : ℝ)^3739 := by
    have hnat : (387883521 : ℕ)^4763*20000000000000^3739 ≤ 5985341716021^3739*1000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387883521 1000000000 5985341716021 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4566014633/10000000000 : ℝ)^4763 ≤ (18418946099997/50000000000000 : ℝ)^3739 := by
    have hnat : (4566014633 : ℕ)^4763*50000000000000^3739 ≤ 18418946099997^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4566014633 10000000000 18418946099997 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211649161/10000000000 : ℝ), (387883521/1000000000 : ℝ), (4566014633/10000000000 : ℝ)] ![(2077212450387/6250000000000 : ℝ), (5985341716021/20000000000000 : ℝ), (18418946099997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211649161/10000000000 : ℝ)|^4763 ≤ (2077212450387/6250000000000 : ℝ)^3739
        have hw : |(4211649161/10000000000 : ℝ)|=(4211649161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(387883521/1000000000 : ℝ)|^4763 ≤ (5985341716021/20000000000000 : ℝ)^3739
        have hw : |(387883521/1000000000 : ℝ)|=(387883521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4566014633/10000000000 : ℝ)|^4763 ≤ (18418946099997/50000000000000 : ℝ)^3739
        have hw : |(4566014633/10000000000 : ℝ)|=(4566014633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s3_4 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1701725669/10000000000 : ℝ)*x 0 + (5182505299/10000000000 : ℝ)*x 1 + (682198951/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1701725669/10000000000 : ℝ)^4763 ≤ (10477393534483/100000000000000 : ℝ)^3739 := by
    have hnat : (1701725669 : ℕ)^4763*100000000000000^3739 ≤ 10477393534483^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701725669 10000000000 10477393534483 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182505299/10000000000 : ℝ)^4763 ≤ (10821831332643/25000000000000 : ℝ)^3739 := by
    have hnat : (5182505299 : ℕ)^4763*25000000000000^3739 ≤ 10821831332643^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182505299 10000000000 10821831332643 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682198951/1250000000 : ℝ)^4763 ≤ (231176405609/500000000000 : ℝ)^3739 := by
    have hnat : (682198951 : ℕ)^4763*500000000000^3739 ≤ 231176405609^3739*1250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682198951 1250000000 231176405609 500000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1701725669/10000000000 : ℝ), (5182505299/10000000000 : ℝ), (682198951/1250000000 : ℝ)] ![(10477393534483/100000000000000 : ℝ), (10821831332643/25000000000000 : ℝ), (231176405609/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1701725669/10000000000 : ℝ)|^4763 ≤ (10477393534483/100000000000000 : ℝ)^3739
        have hw : |(-1701725669/10000000000 : ℝ)|=(1701725669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182505299/10000000000 : ℝ)|^4763 ≤ (10821831332643/25000000000000 : ℝ)^3739
        have hw : |(5182505299/10000000000 : ℝ)|=(5182505299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682198951/1250000000 : ℝ)|^4763 ≤ (231176405609/500000000000 : ℝ)^3739
        have hw : |(682198951/1250000000 : ℝ)|=(682198951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s3_5 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639693939/5000000000 : ℝ)*x 0 + (-1568502357/10000000000 : ℝ)*x 1 + (5457591317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639693939/5000000000 : ℝ)^4763 ≤ (44320793608521/100000000000000 : ℝ)^3739 := by
    have hnat : (2639693939 : ℕ)^4763*100000000000000^3739 ≤ 44320793608521^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639693939 5000000000 44320793608521 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1568502357/10000000000 : ℝ)^4763 ≤ (2360982099291/25000000000000 : ℝ)^3739 := by
    have hnat : (1568502357 : ℕ)^4763*25000000000000^3739 ≤ 2360982099291^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568502357 10000000000 2360982099291 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457591317/10000000000 : ℝ)^4763 ≤ (577940974767/1250000000000 : ℝ)^3739 := by
    have hnat : (5457591317 : ℕ)^4763*1250000000000^3739 ≤ 577940974767^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457591317 10000000000 577940974767 1250000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639693939/5000000000 : ℝ), (-1568502357/10000000000 : ℝ), (5457591317/10000000000 : ℝ)] ![(44320793608521/100000000000000 : ℝ), (2360982099291/25000000000000 : ℝ), (577940974767/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639693939/5000000000 : ℝ)|^4763 ≤ (44320793608521/100000000000000 : ℝ)^3739
        have hw : |(2639693939/5000000000 : ℝ)|=(2639693939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1568502357/10000000000 : ℝ)|^4763 ≤ (2360982099291/25000000000000 : ℝ)^3739
        have hw : |(-1568502357/10000000000 : ℝ)|=(1568502357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457591317/10000000000 : ℝ)|^4763 ≤ (577940974767/1250000000000 : ℝ)^3739
        have hw : |(5457591317/10000000000 : ℝ)|=(5457591317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s3_6 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319846977/2500000000 : ℝ)*x 0 + (682198931/1250000000 : ℝ)*x 1 + (-1568502131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319846977/2500000000 : ℝ)^4763 ≤ (44320793929347/100000000000000 : ℝ)^3739 := by
    have hnat : (1319846977 : ℕ)^4763*100000000000000^3739 ≤ 44320793929347^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319846977 2500000000 44320793929347 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682198931/1250000000 : ℝ)^4763 ≤ (23117639697549/50000000000000 : ℝ)^3739 := by
    have hnat : (682198931 : ℕ)^4763*50000000000000^3739 ≤ 23117639697549^3739*1250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682198931 1250000000 23117639697549 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1568502131/10000000000 : ℝ)^4763 ≤ (1888785332751/20000000000000 : ℝ)^3739 := by
    have hnat : (1568502131 : ℕ)^4763*20000000000000^3739 ≤ 1888785332751^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568502131 10000000000 1888785332751 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319846977/2500000000 : ℝ), (682198931/1250000000 : ℝ), (-1568502131/10000000000 : ℝ)] ![(44320793929347/100000000000000 : ℝ), (23117639697549/50000000000000 : ℝ), (1888785332751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319846977/2500000000 : ℝ)|^4763 ≤ (44320793929347/100000000000000 : ℝ)^3739
        have hw : |(1319846977/2500000000 : ℝ)|=(1319846977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682198931/1250000000 : ℝ)|^4763 ≤ (23117639697549/50000000000000 : ℝ)^3739
        have hw : |(682198931/1250000000 : ℝ)|=(682198931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1568502131/10000000000 : ℝ)|^4763 ≤ (1888785332751/20000000000000 : ℝ)^3739
        have hw : |(-1568502131/10000000000 : ℝ)|=(1568502131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s3_7 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (421182321/1000000000 : ℝ)*x 0 + (1140221739/2500000000 : ℝ)*x 1 + (3884017341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421182321/1000000000 : ℝ)^4763 ≤ (664742976853/2000000000000 : ℝ)^3739 := by
    have hnat : (421182321 : ℕ)^4763*2000000000000^3739 ≤ 664742976853^3739*1000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421182321 1000000000 664742976853 2000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140221739/2500000000 : ℝ)^4763 ≤ (36785201199893/100000000000000 : ℝ)^3739 := by
    have hnat : (1140221739 : ℕ)^4763*100000000000000^3739 ≤ 36785201199893^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140221739 2500000000 36785201199893 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3884017341/10000000000 : ℝ)^4763 ≤ (5995529988327/20000000000000 : ℝ)^3739 := by
    have hnat : (3884017341 : ℕ)^4763*20000000000000^3739 ≤ 5995529988327^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3884017341 10000000000 5995529988327 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(421182321/1000000000 : ℝ), (1140221739/2500000000 : ℝ), (3884017341/10000000000 : ℝ)] ![(664742976853/2000000000000 : ℝ), (36785201199893/100000000000000 : ℝ), (5995529988327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(421182321/1000000000 : ℝ)|^4763 ≤ (664742976853/2000000000000 : ℝ)^3739
        have hw : |(421182321/1000000000 : ℝ)|=(421182321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1140221739/2500000000 : ℝ)|^4763 ≤ (36785201199893/100000000000000 : ℝ)^3739
        have hw : |(1140221739/2500000000 : ℝ)|=(1140221739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3884017341/10000000000 : ℝ)|^4763 ≤ (5995529988327/20000000000000 : ℝ)^3739
        have hw : |(3884017341/10000000000 : ℝ)|=(3884017341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1611_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1649/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10431/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (511/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1649/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1649/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1649/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1649/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1649/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1649/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10307/100000 : ℝ) ^ (4759/1024 : ℝ) ≤ (1295808447363401/50000000000000000000 : ℝ) := by
    have hpowers : (10307/100000 : ℝ)^4759 ≤ (1295808447363401/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10307 : ℕ)^4759*50000000000000000000^1024 ≤ 1295808447363401^1024*100000^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10307 100000 1295808447363401 50000000000000000000 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10307/100000 : ℝ)) (X := (1295808447363401/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1649/10000 : ℝ) ^ (4759/1024 : ℝ) ≤ (4603557479676977/20000000000000000000 : ℝ) := by
    have hpowers : (1649/10000 : ℝ)^4759 ≤ (4603557479676977/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1649 : ℕ)^4759*20000000000000000000^1024 ≤ 4603557479676977^1024*10000^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1649 10000 4603557479676977 20000000000000000000 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1649/10000 : ℝ)) (X := (4603557479676977/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001295808447363401/25000000000000000000 : ℝ) ≤ (10000111526023279/10000000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (25001295808447363401/25000000000000000000 : ℝ)^1024 ≤ (10000111526023279/10000000000000000 : ℝ)^4759 := by
      have hnat : (25001295808447363401 : ℕ)^1024*10000000000000000^4759 ≤ 10000111526023279^4759*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001295808447363401 25000000000000000000 10000111526023279 10000000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000111526023279/10000000000000000 : ℝ)) (X := (25001295808447363401/25000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025609404293111687/100000000000000000000 : ℝ) ≤ (10000550985396389/10000000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (100025609404293111687/100000000000000000000 : ℝ)^1024 ≤ (10000550985396389/10000000000000000 : ℝ)^4759 := by
      have hnat : (100025609404293111687 : ℕ)^1024*10000000000000000^4759 ≤ 10000550985396389^4759*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025609404293111687 100000000000000000000 10000550985396389 10000000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000550985396389/10000000000000000 : ℝ)) (X := (100025609404293111687/100000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004603557479676977/10000000000000000000 : ℝ) ≤ (10000990444769499/10000000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (10004603557479676977/10000000000000000000 : ℝ)^1024 ≤ (10000990444769499/10000000000000000 : ℝ)^4759 := by
      have hnat : (10004603557479676977 : ℕ)^1024*10000000000000000^4759 ≤ 10000990444769499^4759*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004603557479676977 10000000000000000000 10000990444769499 10000000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000990444769499/10000000000000000 : ℝ)) (X := (10004603557479676977/10000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1295808447363401/50000000000000000000 : ℝ) ≤ ((61821630549884644517/61830000000000000000 : ℝ)+2*(43945937311/61830000000000 : ℝ)*(10307/100000 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (61821630549884644517/61830000000000000000 : ℝ)+2*(43945937311/61830000000000 : ℝ)*(10307/100000 : ℝ)=(10000111526023279/10000000000000000 : ℝ) by norm_num, show 1+2*(1295808447363401/50000000000000000000 : ℝ)=(25001295808447363401/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4603557479676977/20000000000000000000 : ℝ)+(1295808447363401/50000000000000000000 : ℝ) ≤ ((61821630549884644517/61830000000000000000 : ℝ)+(43945937311/61830000000000 : ℝ)*((1649/10000 : ℝ)+(10307/100000 : ℝ)))^(4759/1024 : ℝ) := by
    rw [show (61821630549884644517/61830000000000000000 : ℝ)+(43945937311/61830000000000 : ℝ)*((1649/10000 : ℝ)+(10307/100000 : ℝ))=(10000550985396389/10000000000000000 : ℝ) by norm_num, show 1+(4603557479676977/20000000000000000000 : ℝ)+(1295808447363401/50000000000000000000 : ℝ)=(100025609404293111687/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4603557479676977/20000000000000000000 : ℝ) ≤ ((61821630549884644517/61830000000000000000 : ℝ)+2*(43945937311/61830000000000 : ℝ)*(1649/10000 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (61821630549884644517/61830000000000000000 : ℝ)+2*(43945937311/61830000000000 : ℝ)*(1649/10000 : ℝ)=(10000990444769499/10000000000000000 : ℝ) by norm_num, show 1+2*(4603557479676977/20000000000000000000 : ℝ)=(10004603557479676977/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (61821630549884644517/61830000000000000000 : ℝ)*(X 1 0+X 2 0)+(43945937311/61830000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (10307/100000 : ℝ)) (hi := (1649/10000 : ℝ)) (c := (61821630549884644517/61830000000000000000 : ℝ)) (alpha := (43945937311/61830000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (61821630549884644517/61830000000000000000 : ℝ)*(X 0 1+X 2 1)+(43945937311/61830000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (10307/100000 : ℝ)) (hi := (1649/10000 : ℝ)) (c := (61821630549884644517/61830000000000000000 : ℝ)) (alpha := (43945937311/61830000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (61821630549884644517/61830000000000000000 : ℝ)*(X 0 2+X 1 2)+(43945937311/61830000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (10307/100000 : ℝ)) (hi := (1649/10000 : ℝ)) (c := (61821630549884644517/61830000000000000000 : ℝ)) (alpha := (43945937311/61830000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-170165487/1000000000 : ℝ)*X 0 0+(2729848579/5000000000 : ℝ)*X 0 1+(2590210837/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338392679/2500000000 : ℝ)*X 1 0+(-369134473/2000000000 : ℝ)*X 1 1+(5180421437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338392703/2500000000 : ℝ)*X 2 0+(5180421233/10000000000 : ℝ)*X 2 1+(-461418127/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4211649161/10000000000 : ℝ)*X 0 0+(387883521/1000000000 : ℝ)*X 0 1+(4566014633/10000000000 : ℝ)*X 0 2+(4211649161/10000000000 : ℝ)*X 1 0+(387883521/1000000000 : ℝ)*X 1 1+(4566014633/10000000000 : ℝ)*X 1 2+(4211649161/10000000000 : ℝ)*X 2 0+(387883521/1000000000 : ℝ)*X 2 1+(4566014633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1701725669/10000000000 : ℝ)*X 0 0+(5182505299/10000000000 : ℝ)*X 0 1+(682198951/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639693939/5000000000 : ℝ)*X 1 0+(-1568502357/10000000000 : ℝ)*X 1 1+(5457591317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319846977/2500000000 : ℝ)*X 2 0+(682198931/1250000000 : ℝ)*X 2 1+(-1568502131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((421182321/1000000000 : ℝ)*X 0 0+(1140221739/2500000000 : ℝ)*X 0 1+(3884017341/10000000000 : ℝ)*X 0 2+(421182321/1000000000 : ℝ)*X 1 0+(1140221739/2500000000 : ℝ)*X 1 1+(3884017341/10000000000 : ℝ)*X 1 2+(421182321/1000000000 : ℝ)*X 2 0+(1140221739/2500000000 : ℝ)*X 2 1+(3884017341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2511142157118511251856422233/1030500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17616777/5000000000000 : ℝ)*(base19) + (401599507/100000000000000 : ℝ)*(base23) + (5309277/6250000000000 : ℝ)*(upper3) + (304157/12500000000000 : ℝ)*(lower4) + (856863/1250000000000 : ℝ)*(upper5) + (2517959718812251/100000000000000 : ℝ)*(major0) + (2517959718812251/100000000000000 : ℝ)*(major1) + (2517959718812251/100000000000000 : ℝ)*(major2) + (1790347019529613/50000000000000 : ℝ)*(sp0) + (1790346843361843/50000000000000 : ℝ)*(sp1) + (3580692230922601/100000000000000 : ℝ)*(sp2) + (727612282350549/50000000000000 : ℝ)*(sp3) + (703268559/50000000000000 : ℝ)*(sp6) + (752636867/100000000000000 : ℝ)*(sp7) + (291045063467593/20000000000000 : ℝ)*(f.failure) + (1790347019529613/50000000000000 : ℝ)*(f.sum) + (4041774655699/3091500000000000000000000000 : ℝ)*base65 + (4179062849680192589/2061000000000000000000000000000000 : ℝ)*base67 + (15697178032915192589/2061000000000000000000000000000000 : ℝ)*base69 + (16705833454756192589/2061000000000000000000000000000000 : ℝ)*base71 + (4337553463891/1545750000000000000000000000 : ℝ)*base74 + (1429716423022807411/2061000000000000000000000000000000 : ℝ)*base76 + (4138939136023807411/2061000000000000000000000000000000 : ℝ)*base78 + (2725080546151192589/2061000000000000000000000000000000 : ℝ)*base79 + (8148503661677/6183000000000000000000000000 : ℝ)*base81 + (1267049/250000000000000000000 : ℝ)*base90 + (1267049/250000000000000000000 : ℝ)*base92 + (1267049/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (243679461605524727542935371/32203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1189034491/100000000000000 : ℝ)*(base19) + (153141457/12500000000000 : ℝ)*(base23) + (50829637/100000000000000 : ℝ)*(upper3) + (4046661/50000000000000 : ℝ)*(lower4) + (46225711/20000000000000 : ℝ)*(upper5) + (4992788324591/195312500000 : ℝ)*(major0) + (4992788324591/195312500000 : ℝ)*(major1) + (4992788324591/195312500000 : ℝ)*(major2) + (13836038679/100000000000000 : ℝ)*(sp1) + (13843857651/100000000000000 : ℝ)*(sp2) + (3635226953364443/100000000000000 : ℝ)*(sp4) + (3635211928291273/100000000000000 : ℝ)*(sp5) + (113600371386723/3125000000000 : ℝ)*(sp6) + (18467350484813/1250000000000 : ℝ)*(sp7) + (18467350484813/1250000000000 : ℝ)*(f.failure) + (3635226953364443/100000000000000 : ℝ)*(f.sum) + (181684000163/1236600000000000000000000000 : ℝ)*base66 + (71112110668243667/32203125000000000000000000000000 : ℝ)*base67 + (12761867070566987/2012695312500000000000000000000 : ℝ)*base69 + (41944035293332771/16101562500000000000000000000000 : ℝ)*base71 + (369923570441/772875000000000000000000000 : ℝ)*base74 + (3822753594306931/1006347656250000000000000000000 : ℝ)*base75 + (9167090258653927/8050781250000000000000000000000 : ℝ)*base78 + (483258745130837417/32203125000000000000000000000000 : ℝ)*base79 + (7056447230999/1545750000000000000000000000 : ℝ)*base81 + (154509/15625000000000000000 : ℝ)*base90 + (154509/15625000000000000000 : ℝ)*base92 + (154509/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1611_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1649/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (511/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1611_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1611_s4_0 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-850884353/5000000000 : ℝ)*x 0 + (545912631/1000000000 : ℝ)*x 1 + (5180916853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850884353/5000000000 : ℝ)^4763 ≤ (10477731079979/100000000000000 : ℝ)^3739 := by
    have hnat : (850884353 : ℕ)^4763*100000000000000^3739 ≤ 10477731079979^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850884353 5000000000 10477731079979 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545912631/1000000000 : ℝ)^4763 ≤ (9250368819507/20000000000000 : ℝ)^3739 := by
    have hnat : (545912631 : ℕ)^4763*20000000000000^3739 ≤ 9250368819507^3739*1000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545912631 1000000000 9250368819507 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180916853/10000000000 : ℝ)^4763 ≤ (5408803099997/12500000000000 : ℝ)^3739 := by
    have hnat : (5180916853 : ℕ)^4763*12500000000000^3739 ≤ 5408803099997^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180916853 10000000000 5408803099997 12500000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-850884353/5000000000 : ℝ), (545912631/1000000000 : ℝ), (5180916853/10000000000 : ℝ)] ![(10477731079979/100000000000000 : ℝ), (9250368819507/20000000000000 : ℝ), (5408803099997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-850884353/5000000000 : ℝ)|^4763 ≤ (10477731079979/100000000000000 : ℝ)^3739
        have hw : |(-850884353/5000000000 : ℝ)|=(850884353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545912631/1000000000 : ℝ)|^4763 ≤ (9250368819507/20000000000000 : ℝ)^3739
        have hw : |(545912631/1000000000 : ℝ)|=(545912631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180916853/10000000000 : ℝ)|^4763 ≤ (5408803099997/12500000000000 : ℝ)^3739
        have hw : |(5180916853/10000000000 : ℝ)|=(5180916853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s4_1 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676709057/5000000000 : ℝ)*x 0 + (-1845219797/10000000000 : ℝ)*x 1 + (259045827/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676709057/5000000000 : ℝ)^4763 ≤ (2819625264257/6250000000000 : ℝ)^3739 := by
    have hnat : (2676709057 : ℕ)^4763*6250000000000^3739 ≤ 2819625264257^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676709057 5000000000 2819625264257 6250000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1845219797/10000000000 : ℝ)^4763 ≤ (5807787138681/50000000000000 : ℝ)^3739 := by
    have hnat : (1845219797 : ℕ)^4763*50000000000000^3739 ≤ 5807787138681^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845219797 10000000000 5807787138681 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259045827/500000000 : ℝ)^4763 ≤ (43270421469901/100000000000000 : ℝ)^3739 := by
    have hnat : (259045827 : ℕ)^4763*100000000000000^3739 ≤ 43270421469901^3739*500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259045827 500000000 43270421469901 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676709057/5000000000 : ℝ), (-1845219797/10000000000 : ℝ), (259045827/500000000 : ℝ)] ![(2819625264257/6250000000000 : ℝ), (5807787138681/50000000000000 : ℝ), (43270421469901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676709057/5000000000 : ℝ)|^4763 ≤ (2819625264257/6250000000000 : ℝ)^3739
        have hw : |(2676709057/5000000000 : ℝ)|=(2676709057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1845219797/10000000000 : ℝ)|^4763 ≤ (5807787138681/50000000000000 : ℝ)^3739
        have hw : |(-1845219797/10000000000 : ℝ)|=(1845219797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259045827/500000000 : ℝ)|^4763 ≤ (43270421469901/100000000000000 : ℝ)^3739
        have hw : |(259045827/500000000 : ℝ)|=(259045827/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s4_2 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353418321/10000000000 : ℝ)*x 0 + (1036183299/2000000000 : ℝ)*x 1 + (-92260979/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353418321/10000000000 : ℝ)^4763 ≤ (22557003225137/50000000000000 : ℝ)^3739 := by
    have hnat : (5353418321 : ℕ)^4763*50000000000000^3739 ≤ 22557003225137^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353418321 10000000000 22557003225137 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036183299/2000000000 : ℝ)^4763 ≤ (43270420991137/100000000000000 : ℝ)^3739 := by
    have hnat : (1036183299 : ℕ)^4763*100000000000000^3739 ≤ 43270420991137^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036183299 2000000000 43270420991137 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92260979/500000000 : ℝ)^4763 ≤ (11615572537249/100000000000000 : ℝ)^3739 := by
    have hnat : (92260979 : ℕ)^4763*100000000000000^3739 ≤ 11615572537249^3739*500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92260979 500000000 11615572537249 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353418321/10000000000 : ℝ), (1036183299/2000000000 : ℝ), (-92260979/500000000 : ℝ)] ![(22557003225137/50000000000000 : ℝ), (43270420991137/100000000000000 : ℝ), (11615572537249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353418321/10000000000 : ℝ)|^4763 ≤ (22557003225137/50000000000000 : ℝ)^3739
        have hw : |(5353418321/10000000000 : ℝ)|=(5353418321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036183299/2000000000 : ℝ)|^4763 ≤ (43270420991137/100000000000000 : ℝ)^3739
        have hw : |(1036183299/2000000000 : ℝ)|=(1036183299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-92260979/500000000 : ℝ)|^4763 ≤ (11615572537249/100000000000000 : ℝ)^3739
        have hw : |(-92260979/500000000 : ℝ)|=(92260979/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s4_3 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4211723453/10000000000 : ℝ)*x 0 + (3880139699/10000000000 : ℝ)*x 1 + (4564694357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211723453/10000000000 : ℝ)^4763 ≤ (33236146027893/100000000000000 : ℝ)^3739 := by
    have hnat : (4211723453 : ℕ)^4763*100000000000000^3739 ≤ 33236146027893^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211723453 10000000000 33236146027893 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3880139699/10000000000 : ℝ)^4763 ≤ (14969765103889/50000000000000 : ℝ)^3739 := by
    have hnat : (3880139699 : ℕ)^4763*50000000000000^3739 ≤ 14969765103889^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3880139699 10000000000 14969765103889 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4564694357/10000000000 : ℝ)^4763 ≤ (36824323753659/100000000000000 : ℝ)^3739 := by
    have hnat : (4564694357 : ℕ)^4763*100000000000000^3739 ≤ 36824323753659^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564694357 10000000000 36824323753659 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211723453/10000000000 : ℝ), (3880139699/10000000000 : ℝ), (4564694357/10000000000 : ℝ)] ![(33236146027893/100000000000000 : ℝ), (14969765103889/50000000000000 : ℝ), (36824323753659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211723453/10000000000 : ℝ)|^4763 ≤ (33236146027893/100000000000000 : ℝ)^3739
        have hw : |(4211723453/10000000000 : ℝ)|=(4211723453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3880139699/10000000000 : ℝ)|^4763 ≤ (14969765103889/50000000000000 : ℝ)^3739
        have hw : |(3880139699/10000000000 : ℝ)|=(3880139699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4564694357/10000000000 : ℝ)|^4763 ≤ (36824323753659/100000000000000 : ℝ)^3739
        have hw : |(4564694357/10000000000 : ℝ)|=(4564694357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s4_4 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1701838941/10000000000 : ℝ)*x 0 + (5182985079/10000000000 : ℝ)*x 1 + (68212953/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1701838941/10000000000 : ℝ)^4763 ≤ (5239140974197/50000000000000 : ℝ)^3739 := by
    have hnat : (1701838941 : ℕ)^4763*50000000000000^3739 ≤ 5239140974197^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701838941 10000000000 5239140974197 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182985079/10000000000 : ℝ)^4763 ≤ (43292430307213/100000000000000 : ℝ)^3739 := by
    have hnat : (5182985079 : ℕ)^4763*100000000000000^3739 ≤ 43292430307213^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182985079 10000000000 43292430307213 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68212953/125000000 : ℝ)^4763 ≤ (46229287733923/100000000000000 : ℝ)^3739 := by
    have hnat : (68212953 : ℕ)^4763*100000000000000^3739 ≤ 46229287733923^3739*125000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68212953 125000000 46229287733923 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1701838941/10000000000 : ℝ), (5182985079/10000000000 : ℝ), (68212953/125000000 : ℝ)] ![(5239140974197/50000000000000 : ℝ), (43292430307213/100000000000000 : ℝ), (46229287733923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1701838941/10000000000 : ℝ)|^4763 ≤ (5239140974197/50000000000000 : ℝ)^3739
        have hw : |(-1701838941/10000000000 : ℝ)|=(1701838941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182985079/10000000000 : ℝ)|^4763 ≤ (43292430307213/100000000000000 : ℝ)^3739
        have hw : |(5182985079/10000000000 : ℝ)|=(5182985079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68212953/125000000 : ℝ)|^4763 ≤ (46229287733923/100000000000000 : ℝ)^3739
        have hw : |(68212953/125000000 : ℝ)|=(68212953/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s4_5 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279519191/10000000000 : ℝ)*x 0 + (-1569100237/10000000000 : ℝ)*x 1 + (68212953/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279519191/10000000000 : ℝ)^4763 ≤ (11080549475821/25000000000000 : ℝ)^3739 := by
    have hnat : (5279519191 : ℕ)^4763*25000000000000^3739 ≤ 11080549475821^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279519191 10000000000 11080549475821 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1569100237/10000000000 : ℝ)^4763 ≤ (1889702869439/20000000000000 : ℝ)^3739 := by
    have hnat : (1569100237 : ℕ)^4763*20000000000000^3739 ≤ 1889702869439^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569100237 10000000000 1889702869439 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68212953/125000000 : ℝ)^4763 ≤ (46229287733923/100000000000000 : ℝ)^3739 := by
    have hnat : (68212953 : ℕ)^4763*100000000000000^3739 ≤ 46229287733923^3739*125000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68212953 125000000 46229287733923 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279519191/10000000000 : ℝ), (-1569100237/10000000000 : ℝ), (68212953/125000000 : ℝ)] ![(11080549475821/25000000000000 : ℝ), (1889702869439/20000000000000 : ℝ), (46229287733923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279519191/10000000000 : ℝ)|^4763 ≤ (11080549475821/25000000000000 : ℝ)^3739
        have hw : |(5279519191/10000000000 : ℝ)|=(5279519191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1569100237/10000000000 : ℝ)|^4763 ≤ (1889702869439/20000000000000 : ℝ)^3739
        have hw : |(-1569100237/10000000000 : ℝ)|=(1569100237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68212953/125000000 : ℝ)|^4763 ≤ (46229287733923/100000000000000 : ℝ)^3739
        have hw : |(68212953/125000000 : ℝ)|=(68212953/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s4_6 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055903839/2000000000 : ℝ)*x 0 + (5457036239/10000000000 : ℝ)*x 1 + (-1569100233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055903839/2000000000 : ℝ)^4763 ≤ (44322197946061/100000000000000 : ℝ)^3739 := by
    have hnat : (1055903839 : ℕ)^4763*100000000000000^3739 ≤ 44322197946061^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055903839 2000000000 44322197946061 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457036239/10000000000 : ℝ)^4763 ≤ (46229287723131/100000000000000 : ℝ)^3739 := by
    have hnat : (5457036239 : ℕ)^4763*100000000000000^3739 ≤ 46229287723131^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457036239 10000000000 46229287723131 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1569100233/10000000000 : ℝ)^4763 ≤ (295266072391/3125000000000 : ℝ)^3739 := by
    have hnat : (1569100233 : ℕ)^4763*3125000000000^3739 ≤ 295266072391^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569100233 10000000000 295266072391 3125000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055903839/2000000000 : ℝ), (5457036239/10000000000 : ℝ), (-1569100233/10000000000 : ℝ)] ![(44322197946061/100000000000000 : ℝ), (46229287723131/100000000000000 : ℝ), (295266072391/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055903839/2000000000 : ℝ)|^4763 ≤ (44322197946061/100000000000000 : ℝ)^3739
        have hw : |(1055903839/2000000000 : ℝ)|=(1055903839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457036239/10000000000 : ℝ)|^4763 ≤ (46229287723131/100000000000000 : ℝ)^3739
        have hw : |(5457036239/10000000000 : ℝ)|=(5457036239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1569100233/10000000000 : ℝ)|^4763 ≤ (295266072391/3125000000000 : ℝ)^3739
        have hw : |(-1569100233/10000000000 : ℝ)|=(1569100233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s4_7 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052973919/2500000000 : ℝ)*x 0 + (569950733/1250000000 : ℝ)*x 1 + (777056371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052973919/2500000000 : ℝ)^4763 ≤ (33237877316653/100000000000000 : ℝ)^3739 := by
    have hnat : (1052973919 : ℕ)^4763*100000000000000^3739 ≤ 33237877316653^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052973919 2500000000 33237877316653 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569950733/1250000000 : ℝ)^4763 ≤ (143640779229/390625000000 : ℝ)^3739 := by
    have hnat : (569950733 : ℕ)^4763*390625000000^3739 ≤ 143640779229^3739*1250000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569950733 1250000000 143640779229 390625000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (777056371/2000000000 : ℝ)^4763 ≤ (29990083188067/100000000000000 : ℝ)^3739 := by
    have hnat : (777056371 : ℕ)^4763*100000000000000^3739 ≤ 29990083188067^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777056371 2000000000 29990083188067 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052973919/2500000000 : ℝ), (569950733/1250000000 : ℝ), (777056371/2000000000 : ℝ)] ![(33237877316653/100000000000000 : ℝ), (143640779229/390625000000 : ℝ), (29990083188067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052973919/2500000000 : ℝ)|^4763 ≤ (33237877316653/100000000000000 : ℝ)^3739
        have hw : |(1052973919/2500000000 : ℝ)|=(1052973919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569950733/1250000000 : ℝ)|^4763 ≤ (143640779229/390625000000 : ℝ)^3739
        have hw : |(569950733/1250000000 : ℝ)|=(569950733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(777056371/2000000000 : ℝ)|^4763 ≤ (29990083188067/100000000000000 : ℝ)^3739
        have hw : |(777056371/2000000000 : ℝ)|=(777056371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1611_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10441/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (817/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (511/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10431/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (511/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10431/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (511/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10431/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (511/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10431/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (511/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10431/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (511/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10431/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10431/100000 : ℝ) ^ (4759/1024 : ℝ) ≤ (2739732603079131/100000000000000000000 : ℝ) := by
    have hpowers : (10431/100000 : ℝ)^4759 ≤ (2739732603079131/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10431 : ℕ)^4759*100000000000000000000^1024 ≤ 2739732603079131^1024*100000^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10431 100000 2739732603079131 100000000000000000000 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10431/100000 : ℝ)) (X := (2739732603079131/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (511/3125 : ℝ) ^ (4759/1024 : ℝ) ≤ (22136113733401471/100000000000000000000 : ℝ) := by
    have hpowers : (511/3125 : ℝ)^4759 ≤ (22136113733401471/100000000000000000000 : ℝ)^1024 := by
      have hnat : (511 : ℕ)^4759*100000000000000000000^1024 ≤ 22136113733401471^1024*3125^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        511 3125 22136113733401471 100000000000000000000 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (511/3125 : ℝ)) (X := (22136113733401471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002739732603079131/50000000000000000000 : ℝ) ≤ (10000117899805143/10000000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (50002739732603079131/50000000000000000000 : ℝ)^1024 ≤ (10000117899805143/10000000000000000 : ℝ)^4759 := by
      have hnat : (50002739732603079131 : ℕ)^1024*10000000000000000^4759 ≤ 10000117899805143^4759*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002739732603079131 50000000000000000000 10000117899805143 10000000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000117899805143/10000000000000000 : ℝ)) (X := (50002739732603079131/50000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012437923168240301/50000000000000000000 : ℝ) ≤ (625033450279007/625000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (50012437923168240301/50000000000000000000 : ℝ)^1024 ≤ (625033450279007/625000000000000 : ℝ)^4759 := by
      have hnat : (50012437923168240301 : ℕ)^1024*625000000000000^4759 ≤ 625033450279007^4759*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012437923168240301 50000000000000000000 625033450279007 625000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625033450279007/625000000000000 : ℝ)) (X := (50012437923168240301/50000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022136113733401471/50000000000000000000 : ℝ) ≤ (10000952509123081/10000000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (50022136113733401471/50000000000000000000 : ℝ)^1024 ≤ (10000952509123081/10000000000000000 : ℝ)^4759 := by
      have hnat : (50022136113733401471 : ℕ)^1024*10000000000000000^4759 ≤ 10000952509123081^4759*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022136113733401471 50000000000000000000 10000952509123081 10000000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000952509123081/10000000000000000 : ℝ)) (X := (50022136113733401471/50000000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2739732603079131/100000000000000000000 : ℝ) ≤ ((2368079690998033617/2368400000000000000 : ℝ)+2*(417304658969/592100000000000 : ℝ)*(10431/100000 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (2368079690998033617/2368400000000000000 : ℝ)+2*(417304658969/592100000000000 : ℝ)*(10431/100000 : ℝ)=(10000117899805143/10000000000000000 : ℝ) by norm_num, show 1+2*(2739732603079131/100000000000000000000 : ℝ)=(50002739732603079131/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22136113733401471/100000000000000000000 : ℝ)+(2739732603079131/100000000000000000000 : ℝ) ≤ ((2368079690998033617/2368400000000000000 : ℝ)+(417304658969/592100000000000 : ℝ)*((511/3125 : ℝ)+(10431/100000 : ℝ)))^(4759/1024 : ℝ) := by
    rw [show (2368079690998033617/2368400000000000000 : ℝ)+(417304658969/592100000000000 : ℝ)*((511/3125 : ℝ)+(10431/100000 : ℝ))=(625033450279007/625000000000000 : ℝ) by norm_num, show 1+(22136113733401471/100000000000000000000 : ℝ)+(2739732603079131/100000000000000000000 : ℝ)=(50012437923168240301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22136113733401471/100000000000000000000 : ℝ) ≤ ((2368079690998033617/2368400000000000000 : ℝ)+2*(417304658969/592100000000000 : ℝ)*(511/3125 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (2368079690998033617/2368400000000000000 : ℝ)+2*(417304658969/592100000000000 : ℝ)*(511/3125 : ℝ)=(10000952509123081/10000000000000000 : ℝ) by norm_num, show 1+2*(22136113733401471/100000000000000000000 : ℝ)=(50022136113733401471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2368079690998033617/2368400000000000000 : ℝ)*(X 1 0+X 2 0)+(417304658969/592100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (10431/100000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (2368079690998033617/2368400000000000000 : ℝ)) (alpha := (417304658969/592100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2368079690998033617/2368400000000000000 : ℝ)*(X 0 1+X 2 1)+(417304658969/592100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (10431/100000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (2368079690998033617/2368400000000000000 : ℝ)) (alpha := (417304658969/592100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2368079690998033617/2368400000000000000 : ℝ)*(X 0 2+X 1 2)+(417304658969/592100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (10431/100000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (2368079690998033617/2368400000000000000 : ℝ)) (alpha := (417304658969/592100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-850884353/5000000000 : ℝ)*X 0 0+(545912631/1000000000 : ℝ)*X 0 1+(5180916853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676709057/5000000000 : ℝ)*X 1 0+(-1845219797/10000000000 : ℝ)*X 1 1+(259045827/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353418321/10000000000 : ℝ)*X 2 0+(1036183299/2000000000 : ℝ)*X 2 1+(-92260979/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4211723453/10000000000 : ℝ)*X 0 0+(3880139699/10000000000 : ℝ)*X 0 1+(4564694357/10000000000 : ℝ)*X 0 2+(4211723453/10000000000 : ℝ)*X 1 0+(3880139699/10000000000 : ℝ)*X 1 1+(4564694357/10000000000 : ℝ)*X 1 2+(4211723453/10000000000 : ℝ)*X 2 0+(3880139699/10000000000 : ℝ)*X 2 1+(4564694357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1701838941/10000000000 : ℝ)*X 0 0+(5182985079/10000000000 : ℝ)*X 0 1+(68212953/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279519191/10000000000 : ℝ)*X 1 0+(-1569100237/10000000000 : ℝ)*X 1 1+(68212953/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055903839/2000000000 : ℝ)*X 2 0+(5457036239/10000000000 : ℝ)*X 2 1+(-1569100233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052973919/2500000000 : ℝ)*X 0 0+(569950733/1250000000 : ℝ)*X 0 1+(777056371/2000000000 : ℝ)*X 0 2+(1052973919/2500000000 : ℝ)*X 1 0+(569950733/1250000000 : ℝ)*X 1 1+(777056371/2000000000 : ℝ)*X 1 2+(1052973919/2500000000 : ℝ)*X 2 0+(569950733/1250000000 : ℝ)*X 2 1+(777056371/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8543579287689529077731313/955000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (872104631/50000000000000 : ℝ)*(base19) + (1625352593/100000000000000 : ℝ)*(base23) + (138034053/100000000000000 : ℝ)*(lower2) + (175366881/100000000000000 : ℝ)*(upper3) + (85898089/50000000000000 : ℝ)*(upper5) + (1263817032214653/50000000000000 : ℝ)*(major0) + (1263817032214653/50000000000000 : ℝ)*(major1) + (1263817032214653/50000000000000 : ℝ)*(major2) + (898607830697553/25000000000000 : ℝ)*(sp0) + (898612398602021/25000000000000 : ℝ)*(sp1) + (224653107079047/6250000000000 : ℝ)*(sp2) + (730404812859249/50000000000000 : ℝ)*(sp3) + (10007913567/50000000000000 : ℝ)*(sp4) + (6866317551/100000000000000 : ℝ)*(sp7) + (1460816492036049/100000000000000 : ℝ)*(f.failure) + (1797225669308673/50000000000000 : ℝ)*(f.sum) + (1023235727187/477500000000000000000000000 : ℝ)*base65 + (48587072451265229/3820000000000000000000000000000 : ℝ)*base68 + (885176783434771/3820000000000000000000000000000 : ℝ)*base69 + (21097184195945229/3820000000000000000000000000000 : ℝ)*base72 + (373120632937/119375000000000000000000000 : ℝ)*base74 + (28749353207045229/3820000000000000000000000000000 : ℝ)*base76 + (21428331653065229/3820000000000000000000000000000 : ℝ)*base78 + (31908467059145229/3820000000000000000000000000000 : ℝ)*base80 + (430031133411/955000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8653743/1250000000000000000000 : ℝ)*base89 + (8653743/1250000000000000000000 : ℝ)*base91 + (8653743/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96210419176094434813317/14802500000000000000000000000 : ℝ) := by norm_num
    linear_combination (993283081/100000000000000 : ℝ)*(base19) + (1079242533/100000000000000 : ℝ)*(base23) + (12613607/4000000000000 : ℝ)*(lower1) + (135904729/100000000000000 : ℝ)*(upper3) + (7434601/20000000000000 : ℝ)*(lower4) + (67542953/50000000000000 : ℝ)*(upper5) + (1282975926280449/50000000000000 : ℝ)*(major0) + (1282975926280449/50000000000000 : ℝ)*(major1) + (1282975926280449/50000000000000 : ℝ)*(major2) + (913391739/100000000000000 : ℝ)*(sp2) + (456117709967391/12500000000000 : ℝ)*(sp4) + (1824470343228023/50000000000000 : ℝ)*(sp5) + (456117460888107/12500000000000 : ℝ)*(sp6) + (370740452182279/25000000000000 : ℝ)*(sp7) + (370740452182279/25000000000000 : ℝ)*(f.failure) + (456117709967391/12500000000000 : ℝ)*(f.sum) + (62557636673261/14802500000000000000000000000 : ℝ)*base65 + (2265857275931058033/118420000000000000000000000000000 : ℝ)*base67 + (149257230877821967/118420000000000000000000000000000 : ℝ)*base70 + (10550949882719338033/118420000000000000000000000000000 : ℝ)*base71 + (7389547413/7227783203125000000000000 : ℝ)*base74 + (449106201867778033/118420000000000000000000000000000 : ℝ)*base75 + (391932335522921967/118420000000000000000000000000000 : ℝ)*base78 + (117965777671281967/118420000000000000000000000000000 : ℝ)*base80 + (12776975066701/14802500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1394647/312500000000000000000 : ℝ)*base90 + (1394647/312500000000000000000 : ℝ)*base92 + (1394647/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1611_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10441/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (817/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1611_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1611_s5_0 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1701779323/10000000000 : ℝ)*x 0 + (5459078689/10000000000 : ℝ)*x 1 + (1036191467/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1701779323/10000000000 : ℝ)^4763 ≤ (419112574041/4000000000000 : ℝ)^3739 := by
    have hnat : (1701779323 : ℕ)^4763*4000000000000^3739 ≤ 419112574041^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701779323 10000000000 419112574041 4000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459078689/10000000000 : ℝ)^4763 ≤ (11562832534473/25000000000000 : ℝ)^3739 := by
    have hnat : (5459078689 : ℕ)^4763*25000000000000^3739 ≤ 11562832534473^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459078689 10000000000 11562832534473 25000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036191467/2000000000 : ℝ)^4763 ≤ (21635427748603/50000000000000 : ℝ)^3739 := by
    have hnat : (1036191467 : ℕ)^4763*50000000000000^3739 ≤ 21635427748603^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036191467 2000000000 21635427748603 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1701779323/10000000000 : ℝ), (5459078689/10000000000 : ℝ), (1036191467/2000000000 : ℝ)] ![(419112574041/4000000000000 : ℝ), (11562832534473/25000000000000 : ℝ), (21635427748603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1701779323/10000000000 : ℝ)|^4763 ≤ (419112574041/4000000000000 : ℝ)^3739
        have hw : |(-1701779323/10000000000 : ℝ)|=(1701779323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459078689/10000000000 : ℝ)|^4763 ≤ (11562832534473/25000000000000 : ℝ)^3739
        have hw : |(5459078689/10000000000 : ℝ)|=(5459078689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036191467/2000000000 : ℝ)|^4763 ≤ (21635427748603/50000000000000 : ℝ)^3739
        have hw : |(1036191467/2000000000 : ℝ)|=(1036191467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s5_1 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676702479/5000000000 : ℝ)*x 0 + (-922591647/5000000000 : ℝ)*x 1 + (323809833/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676702479/5000000000 : ℝ)^4763 ≤ (45113862997433/100000000000000 : ℝ)^3739 := by
    have hnat : (2676702479 : ℕ)^4763*100000000000000^3739 ≤ 45113862997433^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676702479 5000000000 45113862997433 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922591647/5000000000 : ℝ)^4763 ≤ (5807640781147/50000000000000 : ℝ)^3739 := by
    have hnat : (922591647 : ℕ)^4763*50000000000000^3739 ≤ 5807640781147^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922591647 5000000000 5807640781147 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323809833/625000000 : ℝ)^4763 ≤ (43270855422731/100000000000000 : ℝ)^3739 := by
    have hnat : (323809833 : ℕ)^4763*100000000000000^3739 ≤ 43270855422731^3739*625000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323809833 625000000 43270855422731 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676702479/5000000000 : ℝ), (-922591647/5000000000 : ℝ), (323809833/625000000 : ℝ)] ![(45113862997433/100000000000000 : ℝ), (5807640781147/50000000000000 : ℝ), (43270855422731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676702479/5000000000 : ℝ)|^4763 ≤ (45113862997433/100000000000000 : ℝ)^3739
        have hw : |(2676702479/5000000000 : ℝ)|=(2676702479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-922591647/5000000000 : ℝ)|^4763 ≤ (5807640781147/50000000000000 : ℝ)^3739
        have hw : |(-922591647/5000000000 : ℝ)|=(922591647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323809833/625000000 : ℝ)|^4763 ≤ (43270855422731/100000000000000 : ℝ)^3739
        have hw : |(323809833/625000000 : ℝ)|=(323809833/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s5_2 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676702453/5000000000 : ℝ)*x 0 + (1295239343/2500000000 : ℝ)*x 1 + (-922591653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676702453/5000000000 : ℝ)^4763 ≤ (45113862439209/100000000000000 : ℝ)^3739 := by
    have hnat : (2676702453 : ℕ)^4763*100000000000000^3739 ≤ 45113862439209^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676702453 5000000000 45113862439209 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295239343/2500000000 : ℝ)^4763 ≤ (43270855890857/100000000000000 : ℝ)^3739 := by
    have hnat : (1295239343 : ℕ)^4763*100000000000000^3739 ≤ 43270855890857^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295239343 2500000000 43270855890857 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922591653/5000000000 : ℝ)^4763 ≤ (11615281658521/100000000000000 : ℝ)^3739 := by
    have hnat : (922591653 : ℕ)^4763*100000000000000^3739 ≤ 11615281658521^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922591653 5000000000 11615281658521 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676702453/5000000000 : ℝ), (1295239343/2500000000 : ℝ), (-922591653/5000000000 : ℝ)] ![(45113862439209/100000000000000 : ℝ), (43270855890857/100000000000000 : ℝ), (11615281658521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676702453/5000000000 : ℝ)|^4763 ≤ (45113862439209/100000000000000 : ℝ)^3739
        have hw : |(2676702453/5000000000 : ℝ)|=(2676702453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295239343/2500000000 : ℝ)|^4763 ≤ (43270855890857/100000000000000 : ℝ)^3739
        have hw : |(1295239343/2500000000 : ℝ)|=(1295239343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-922591653/5000000000 : ℝ)|^4763 ≤ (11615281658521/100000000000000 : ℝ)^3739
        have hw : |(-922591653/5000000000 : ℝ)|=(922591653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s5_3 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052932343/2500000000 : ℝ)*x 0 + (388024699/1000000000 : ℝ)*x 1 + (912917189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052932343/2500000000 : ℝ)^4763 ≤ (6647241105781/20000000000000 : ℝ)^3739 := by
    have hnat : (1052932343 : ℕ)^4763*20000000000000^3739 ≤ 6647241105781^3739*2500000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052932343 2500000000 6647241105781 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388024699/1000000000 : ℝ)^4763 ≤ (598811696151/2000000000000 : ℝ)^3739 := by
    have hnat : (388024699 : ℕ)^4763*2000000000000^3739 ≤ 598811696151^3739*1000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388024699 1000000000 598811696151 2000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (912917189/2000000000 : ℝ)^4763 ≤ (18411604826877/50000000000000 : ℝ)^3739 := by
    have hnat : (912917189 : ℕ)^4763*50000000000000^3739 ≤ 18411604826877^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912917189 2000000000 18411604826877 50000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052932343/2500000000 : ℝ), (388024699/1000000000 : ℝ), (912917189/2000000000 : ℝ)] ![(6647241105781/20000000000000 : ℝ), (598811696151/2000000000000 : ℝ), (18411604826877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052932343/2500000000 : ℝ)|^4763 ≤ (6647241105781/20000000000000 : ℝ)^3739
        have hw : |(1052932343/2500000000 : ℝ)|=(1052932343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388024699/1000000000 : ℝ)|^4763 ≤ (598811696151/2000000000000 : ℝ)^3739
        have hw : |(388024699/1000000000 : ℝ)|=(388024699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(912917189/2000000000 : ℝ)|^4763 ≤ (18411604826877/50000000000000 : ℝ)^3739
        have hw : |(912917189/2000000000 : ℝ)|=(912917189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s5_4 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1701849261/10000000000 : ℝ)*x 0 + (5183024361/10000000000 : ℝ)*x 1 + (5456990007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1701849261/10000000000 : ℝ)^4763 ≤ (654897680683/6250000000000 : ℝ)^3739 := by
    have hnat : (1701849261 : ℕ)^4763*6250000000000^3739 ≤ 654897680683^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701849261 10000000000 654897680683 6250000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183024361/10000000000 : ℝ)^4763 ≤ (43292848283041/100000000000000 : ℝ)^3739 := by
    have hnat : (5183024361 : ℕ)^4763*100000000000000^3739 ≤ 43292848283041^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183024361 10000000000 43292848283041 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456990007/10000000000 : ℝ)^4763 ≤ (46228788806871/100000000000000 : ℝ)^3739 := by
    have hnat : (5456990007 : ℕ)^4763*100000000000000^3739 ≤ 46228788806871^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456990007 10000000000 46228788806871 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1701849261/10000000000 : ℝ), (5183024361/10000000000 : ℝ), (5456990007/10000000000 : ℝ)] ![(654897680683/6250000000000 : ℝ), (43292848283041/100000000000000 : ℝ), (46228788806871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1701849261/10000000000 : ℝ)|^4763 ≤ (654897680683/6250000000000 : ℝ)^3739
        have hw : |(-1701849261/10000000000 : ℝ)|=(1701849261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183024361/10000000000 : ℝ)|^4763 ≤ (43292848283041/100000000000000 : ℝ)^3739
        have hw : |(5183024361/10000000000 : ℝ)|=(5183024361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456990007/10000000000 : ℝ)|^4763 ≤ (46228788806871/100000000000000 : ℝ)^3739
        have hw : |(5456990007/10000000000 : ℝ)|=(5456990007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s5_5 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279529611/10000000000 : ℝ)*x 0 + (-62766023/400000000 : ℝ)*x 1 + (5456990133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279529611/10000000000 : ℝ)^4763 ≤ (8864461867567/20000000000000 : ℝ)^3739 := by
    have hnat : (5279529611 : ℕ)^4763*20000000000000^3739 ≤ 8864461867567^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279529611 10000000000 8864461867567 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62766023/400000000 : ℝ)^4763 ≤ (9448900479217/100000000000000 : ℝ)^3739 := by
    have hnat : (62766023 : ℕ)^4763*100000000000000^3739 ≤ 9448900479217^3739*400000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62766023 400000000 9448900479217 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456990133/10000000000 : ℝ)^4763 ≤ (2889299385413/6250000000000 : ℝ)^3739 := by
    have hnat : (5456990133 : ℕ)^4763*6250000000000^3739 ≤ 2889299385413^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456990133 10000000000 2889299385413 6250000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279529611/10000000000 : ℝ), (-62766023/400000000 : ℝ), (5456990133/10000000000 : ℝ)] ![(8864461867567/20000000000000 : ℝ), (9448900479217/100000000000000 : ℝ), (2889299385413/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279529611/10000000000 : ℝ)|^4763 ≤ (8864461867567/20000000000000 : ℝ)^3739
        have hw : |(5279529611/10000000000 : ℝ)|=(5279529611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-62766023/400000000 : ℝ)|^4763 ≤ (9448900479217/100000000000000 : ℝ)^3739
        have hw : |(-62766023/400000000 : ℝ)|=(62766023/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456990133/10000000000 : ℝ)|^4763 ≤ (2889299385413/6250000000000 : ℝ)^3739
        have hw : |(5456990133/10000000000 : ℝ)|=(5456990133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s5_6 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279529543/10000000000 : ℝ)*x 0 + (8526547/15625000 : ℝ)*x 1 + (-784575373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279529543/10000000000 : ℝ)^4763 ≤ (44322308610623/100000000000000 : ℝ)^3739 := by
    have hnat : (5279529543 : ℕ)^4763*100000000000000^3739 ≤ 44322308610623^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279529543 10000000000 44322308610623 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8526547/15625000 : ℝ)^4763 ≤ (9245757918931/20000000000000 : ℝ)^3739 := by
    have hnat : (8526547 : ℕ)^4763*20000000000000^3739 ≤ 9245757918931^3739*15625000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8526547 15625000 9245757918931 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (784575373/5000000000 : ℝ)^4763 ≤ (9448901790927/100000000000000 : ℝ)^3739 := by
    have hnat : (784575373 : ℕ)^4763*100000000000000^3739 ≤ 9448901790927^3739*5000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784575373 5000000000 9448901790927 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279529543/10000000000 : ℝ), (8526547/15625000 : ℝ), (-784575373/5000000000 : ℝ)] ![(44322308610623/100000000000000 : ℝ), (9245757918931/20000000000000 : ℝ), (9448901790927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279529543/10000000000 : ℝ)|^4763 ≤ (44322308610623/100000000000000 : ℝ)^3739
        have hw : |(5279529543/10000000000 : ℝ)|=(5279529543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8526547/15625000 : ℝ)|^4763 ≤ (9245757918931/20000000000000 : ℝ)^3739
        have hw : |(8526547/15625000 : ℝ)|=(8526547/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-784575373/5000000000 : ℝ)|^4763 ≤ (9448901790927/100000000000000 : ℝ)^3739
        have hw : |(-784575373/5000000000 : ℝ)|=(784575373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1611_s5_7 (p : ℝ) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4211901601/10000000000 : ℝ)*x 0 + (911900039/2000000000 : ℝ)*x 1 + (19426931/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211901601/10000000000 : ℝ)^4763 ≤ (33237936878647/100000000000000 : ℝ)^3739 := by
    have hnat : (4211901601 : ℕ)^4763*100000000000000^3739 ≤ 33237936878647^3739*10000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211901601 10000000000 33237936878647 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (911900039/2000000000 : ℝ)^4763 ≤ (36770953902833/100000000000000 : ℝ)^3739 := by
    have hnat : (911900039 : ℕ)^4763*100000000000000^3739 ≤ 36770953902833^3739*2000000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911900039 2000000000 36770953902833 100000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19426931/50000000 : ℝ)^4763 ≤ (5998221840513/20000000000000 : ℝ)^3739 := by
    have hnat : (19426931 : ℕ)^4763*20000000000000^3739 ≤ 5998221840513^3739*50000000^4763 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19426931 50000000 5998221840513 20000000000000 4763 3739 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4763/1024 : ℝ)) 4763 3739 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211901601/10000000000 : ℝ), (911900039/2000000000 : ℝ), (19426931/50000000 : ℝ)] ![(33237936878647/100000000000000 : ℝ), (36770953902833/100000000000000 : ℝ), (5998221840513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211901601/10000000000 : ℝ)|^4763 ≤ (33237936878647/100000000000000 : ℝ)^3739
        have hw : |(4211901601/10000000000 : ℝ)|=(4211901601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(911900039/2000000000 : ℝ)|^4763 ≤ (36770953902833/100000000000000 : ℝ)^3739
        have hw : |(911900039/2000000000 : ℝ)|=(911900039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19426931/50000000 : ℝ)|^4763 ≤ (5998221840513/20000000000000 : ℝ)^3739
        have hw : |(19426931/50000000 : ℝ)|=(19426931/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1611_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (817/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5221/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16339/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (817/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10441/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (817/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10441/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (817/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10441/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (817/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10441/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (817/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10441/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (817/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10441/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10441/100000 : ℝ) ^ (4759/1024 : ℝ) ≤ (343995081857089/12500000000000000000 : ℝ) := by
    have hpowers : (10441/100000 : ℝ)^4759 ≤ (343995081857089/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10441 : ℕ)^4759*12500000000000000000^1024 ≤ 343995081857089^1024*100000^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10441 100000 343995081857089 12500000000000000000 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10441/100000 : ℝ)) (X := (343995081857089/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (817/5000 : ℝ) ^ (4759/1024 : ℝ) ≤ (1378794880741121/6250000000000000000 : ℝ) := by
    have hpowers : (817/5000 : ℝ)^4759 ≤ (1378794880741121/6250000000000000000 : ℝ)^1024 := by
      have hnat : (817 : ℕ)^4759*6250000000000000000^1024 ≤ 1378794880741121^1024*5000^4759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        817 5000 1378794880741121 6250000000000000000 4759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (817/5000 : ℝ)) (X := (1378794880741121/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250343995081857089/6250000000000000000 : ℝ) ≤ (1250014803250939/1250000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (6250343995081857089/6250000000000000000 : ℝ)^1024 ≤ (1250014803250939/1250000000000000 : ℝ)^4759 := by
      have hnat : (6250343995081857089 : ℕ)^1024*1250000000000000^4759 ≤ 1250014803250939^4759*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250343995081857089 6250000000000000000 1250014803250939 1250000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250014803250939/1250000000000000 : ℝ)) (X := (6250343995081857089/6250000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503101584843339331/12500000000000000000 : ℝ) ≤ (250013346138603/250000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (12503101584843339331/12500000000000000000 : ℝ)^1024 ≤ (250013346138603/250000000000000 : ℝ)^4759 := by
      have hnat : (12503101584843339331 : ℕ)^1024*250000000000000^4759 ≤ 250013346138603^4759*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503101584843339331 12500000000000000000 250013346138603 250000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250013346138603/250000000000000 : ℝ)) (X := (12503101584843339331/12500000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126378794880741121/3125000000000000000 : ℝ) ≤ (1250118658135091/1250000000000000 : ℝ) ^ (4759/1024 : ℝ) := by
    have hpowers : (3126378794880741121/3125000000000000000 : ℝ)^1024 ≤ (1250118658135091/1250000000000000 : ℝ)^4759 := by
      have hnat : (3126378794880741121 : ℕ)^1024*1250000000000000^4759 ≤ 1250118658135091^4759*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126378794880741121 3125000000000000000 1250118658135091 1250000000000000 1024 4759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250118658135091/1250000000000000 : ℝ)) (X := (3126378794880741121/3125000000000000000 : ℝ)) (by norm_num) 4759 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(343995081857089/12500000000000000000 : ℝ) ≤ ((7372752975531858129/7373750000000000000 : ℝ)+2*(12981860519/18434375000000 : ℝ)*(10441/100000 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (7372752975531858129/7373750000000000000 : ℝ)+2*(12981860519/18434375000000 : ℝ)*(10441/100000 : ℝ)=(1250014803250939/1250000000000000 : ℝ) by norm_num, show 1+2*(343995081857089/12500000000000000000 : ℝ)=(6250343995081857089/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1378794880741121/6250000000000000000 : ℝ)+(343995081857089/12500000000000000000 : ℝ) ≤ ((7372752975531858129/7373750000000000000 : ℝ)+(12981860519/18434375000000 : ℝ)*((817/5000 : ℝ)+(10441/100000 : ℝ)))^(4759/1024 : ℝ) := by
    rw [show (7372752975531858129/7373750000000000000 : ℝ)+(12981860519/18434375000000 : ℝ)*((817/5000 : ℝ)+(10441/100000 : ℝ))=(250013346138603/250000000000000 : ℝ) by norm_num, show 1+(1378794880741121/6250000000000000000 : ℝ)+(343995081857089/12500000000000000000 : ℝ)=(12503101584843339331/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1378794880741121/6250000000000000000 : ℝ) ≤ ((7372752975531858129/7373750000000000000 : ℝ)+2*(12981860519/18434375000000 : ℝ)*(817/5000 : ℝ))^(4759/1024 : ℝ) := by
    rw [show (7372752975531858129/7373750000000000000 : ℝ)+2*(12981860519/18434375000000 : ℝ)*(817/5000 : ℝ)=(1250118658135091/1250000000000000 : ℝ) by norm_num, show 1+2*(1378794880741121/6250000000000000000 : ℝ)=(3126378794880741121/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7372752975531858129/7373750000000000000 : ℝ)*(X 1 0+X 2 0)+(12981860519/18434375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (10441/100000 : ℝ)) (hi := (817/5000 : ℝ)) (c := (7372752975531858129/7373750000000000000 : ℝ)) (alpha := (12981860519/18434375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7372752975531858129/7373750000000000000 : ℝ)*(X 0 1+X 2 1)+(12981860519/18434375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (10441/100000 : ℝ)) (hi := (817/5000 : ℝ)) (c := (7372752975531858129/7373750000000000000 : ℝ)) (alpha := (12981860519/18434375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7372752975531858129/7373750000000000000 : ℝ)*(X 0 2+X 1 2)+(12981860519/18434375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4759/1024 : ℝ)) (lo := (10441/100000 : ℝ)) (hi := (817/5000 : ℝ)) (c := (7372752975531858129/7373750000000000000 : ℝ)) (alpha := (12981860519/18434375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1701779323/10000000000 : ℝ)*X 0 0+(5459078689/10000000000 : ℝ)*X 0 1+(1036191467/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676702479/5000000000 : ℝ)*X 1 0+(-922591647/5000000000 : ℝ)*X 1 1+(323809833/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676702453/5000000000 : ℝ)*X 2 0+(1295239343/2500000000 : ℝ)*X 2 1+(-922591653/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1052932343/2500000000 : ℝ)*X 0 0+(388024699/1000000000 : ℝ)*X 0 1+(912917189/2000000000 : ℝ)*X 0 2+(1052932343/2500000000 : ℝ)*X 1 0+(388024699/1000000000 : ℝ)*X 1 1+(912917189/2000000000 : ℝ)*X 1 2+(1052932343/2500000000 : ℝ)*X 2 0+(388024699/1000000000 : ℝ)*X 2 1+(912917189/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1701849261/10000000000 : ℝ)*X 0 0+(5183024361/10000000000 : ℝ)*X 0 1+(5456990007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279529611/10000000000 : ℝ)*X 1 0+(-62766023/400000000 : ℝ)*X 1 1+(5456990133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279529543/10000000000 : ℝ)*X 2 0+(8526547/15625000 : ℝ)*X 2 1+(-784575373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211901601/10000000000 : ℝ)*X 0 0+(911900039/2000000000 : ℝ)*X 0 1+(19426931/50000000 : ℝ)*X 0 2+(4211901601/10000000000 : ℝ)*X 1 0+(911900039/2000000000 : ℝ)*X 1 1+(19426931/50000000 : ℝ)*X 1 2+(4211901601/10000000000 : ℝ)*X 2 0+(911900039/2000000000 : ℝ)*X 2 1+(19426931/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1611_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (743586141913782036917182683/92171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1382721079/100000000000000 : ℝ)*(base19) + (1256548951/100000000000000 : ℝ)*(base23) + (9769601/20000000000000 : ℝ)*(lower2) + (8383521/4000000000000 : ℝ)*(upper3) + (64465383/50000000000000 : ℝ)*(upper5) + (316054054477789/12500000000000 : ℝ)*(major0) + (316054054477789/12500000000000 : ℝ)*(major1) + (316054054477789/12500000000000 : ℝ)*(major2) + (3595570245488607/100000000000000 : ℝ)*(sp0) + (898896329645571/25000000000000 : ℝ)*(sp1) + (3595585444754411/100000000000000 : ℝ)*(sp2) + (1461270597058391/100000000000000 : ℝ)*(sp3) + (3291162951/20000000000000 : ℝ)*(sp4) + (7304369977/100000000000000 : ℝ)*(sp7) + (91329868839273/6250000000000 : ℝ)*(f.failure) + (1797793350651681/50000000000000 : ℝ)*(f.sum) + (83364620563239/29495000000000000000000000000 : ℝ)*base66 + (2025149646030929/677734375000000000000000000000 : ℝ)*base68 + (20143629765951841/2710937500000000000000000000000 : ℝ)*base70 + (48690317196201841/2710937500000000000000000000000 : ℝ)*base72 + (105627523857741/29495000000000000000000000000 : ℝ)*base73 + (14989820347999679/677734375000000000000000000000 : ℝ)*base76 + (20435954590358733/1355468750000000000000000000000 : ℝ)*base78 + (25086587760358091/2710937500000000000000000000000 : ℝ)*base80 + (17983307737841/29495000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (632711/78125000000000000000 : ℝ)*base89 + (632711/78125000000000000000 : ℝ)*base91 + (632711/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (623149197255232223407057863/92171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (432099981/50000000000000 : ℝ)*(base19) + (934537129/100000000000000 : ℝ)*(base23) + (286532073/100000000000000 : ℝ)*(lower1) + (3758891/2500000000000 : ℝ)*(upper3) + (31206477/50000000000000 : ℝ)*(lower4) + (100311747/100000000000000 : ℝ)*(upper5) + (641688060730583/25000000000000 : ℝ)*(major0) + (641688060730583/25000000000000 : ℝ)*(major1) + (641688060730583/25000000000000 : ℝ)*(major2) + (968063/1562500000000 : ℝ)*(sp1) + (912519968881599/25000000000000 : ℝ)*(sp4) + (1825039474685201/50000000000000 : ℝ)*(sp5) + (912519735247317/25000000000000 : ℝ)*(sp6) + (1483424384960583/100000000000000 : ℝ)*(sp7) + (1483424384960583/100000000000000 : ℝ)*(f.failure) + (912519968881599/25000000000000 : ℝ)*(f.sum) + (115948121066509/29495000000000000000000000000 : ℝ)*base66 + (4488503607269679/10843750000000000000000000000000 : ℝ)*base68 + (97527149159050929/10843750000000000000000000000000 : ℝ)*base70 + (87652768480394679/10843750000000000000000000000000 : ℝ)*base72 + (30948685498991/29495000000000000000000000000 : ℝ)*base73 + (4745000813113429/10843750000000000000000000000000 : ℝ)*base76 + (65956205772957179/10843750000000000000000000000000 : ℝ)*base78 + (33722478105644679/10843750000000000000000000000000 : ℝ)*base80 + (34959209663/921718750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10197881/1250000000000000000000 : ℝ)*base89 + (10197881/1250000000000000000000 : ℝ)*base91 + (10197881/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1611_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (817/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5221/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1611_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1611_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1649/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5221/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1611_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1611_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1611_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4759/1024 : ℝ) ≤ p) (hpb : p ≤ (4763/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21628607/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1649/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5221/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1611_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
