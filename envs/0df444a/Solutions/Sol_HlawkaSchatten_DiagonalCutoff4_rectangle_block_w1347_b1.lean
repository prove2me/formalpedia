-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1347_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:06:35.960335+00:00
-- url     : https://prove2.me/submissions/f559114f-8f13-4313-9b4c-cf56f3bcea01

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
theorem support_rectangle_w1347_s3_0 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037951803/10000000000 : ℝ)*x 0 + (678316563/1250000000 : ℝ)*x 1 + (2615899391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037951803/10000000000 : ℝ)^4307 ≤ (12408654500343/100000000000000 : ℝ)^3283 := by
    have hnat : (2037951803 : ℕ)^4307*100000000000000^3283 ≤ 12408654500343^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037951803 10000000000 12408654500343 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678316563/1250000000 : ℝ)^4307 ≤ (4484534155347/10000000000000 : ℝ)^3283 := by
    have hnat : (678316563 : ℕ)^4307*10000000000000^3283 ≤ 4484534155347^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678316563 1250000000 4484534155347 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615899391/5000000000 : ℝ)^4307 ≤ (42746003931327/100000000000000 : ℝ)^3283 := by
    have hnat : (2615899391 : ℕ)^4307*100000000000000^3283 ≤ 42746003931327^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615899391 5000000000 42746003931327 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037951803/10000000000 : ℝ), (678316563/1250000000 : ℝ), (2615899391/5000000000 : ℝ)] ![(12408654500343/100000000000000 : ℝ), (4484534155347/10000000000000 : ℝ), (42746003931327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037951803/10000000000 : ℝ)|^4307 ≤ (12408654500343/100000000000000 : ℝ)^3283
        have hw : |(-2037951803/10000000000 : ℝ)|=(2037951803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678316563/1250000000 : ℝ)|^4307 ≤ (4484534155347/10000000000000 : ℝ)^3283
        have hw : |(678316563/1250000000 : ℝ)|=(678316563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615899391/5000000000 : ℝ)|^4307 ≤ (42746003931327/100000000000000 : ℝ)^3283
        have hw : |(2615899391/5000000000 : ℝ)|=(2615899391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s3_1 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352505171/10000000000 : ℝ)*x 0 + (-213746269/1000000000 : ℝ)*x 1 + (1046359727/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352505171/10000000000 : ℝ)^4307 ≤ (22022234729331/50000000000000 : ℝ)^3283 := by
    have hnat : (5352505171 : ℕ)^4307*50000000000000^3283 ≤ 22022234729331^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352505171 10000000000 22022234729331 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (213746269/1000000000 : ℝ)^4307 ≤ (13209528170513/100000000000000 : ℝ)^3283 := by
    have hnat : (213746269 : ℕ)^4307*100000000000000^3283 ≤ 13209528170513^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213746269 1000000000 13209528170513 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046359727/2000000000 : ℝ)^4307 ≤ (8549200471131/20000000000000 : ℝ)^3283 := by
    have hnat : (1046359727 : ℕ)^4307*20000000000000^3283 ≤ 8549200471131^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046359727 2000000000 8549200471131 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352505171/10000000000 : ℝ), (-213746269/1000000000 : ℝ), (1046359727/2000000000 : ℝ)] ![(22022234729331/50000000000000 : ℝ), (13209528170513/100000000000000 : ℝ), (8549200471131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352505171/10000000000 : ℝ)|^4307 ≤ (22022234729331/50000000000000 : ℝ)^3283
        have hw : |(5352505171/10000000000 : ℝ)|=(5352505171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-213746269/1000000000 : ℝ)|^4307 ≤ (13209528170513/100000000000000 : ℝ)^3283
        have hw : |(-213746269/1000000000 : ℝ)|=(213746269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046359727/2000000000 : ℝ)|^4307 ≤ (8549200471131/20000000000000 : ℝ)^3283
        have hw : |(1046359727/2000000000 : ℝ)|=(1046359727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s3_2 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676252607/5000000000 : ℝ)*x 0 + (2615899213/5000000000 : ℝ)*x 1 + (-2137462909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676252607/5000000000 : ℝ)^4307 ≤ (2752779370179/6250000000000 : ℝ)^3283 := by
    have hnat : (2676252607 : ℕ)^4307*6250000000000^3283 ≤ 2752779370179^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676252607 5000000000 2752779370179 6250000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615899213/5000000000 : ℝ)^4307 ≤ (21373000057707/50000000000000 : ℝ)^3283 := by
    have hnat : (2615899213 : ℕ)^4307*50000000000000^3283 ≤ 21373000057707^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615899213 5000000000 21373000057707 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2137462909/10000000000 : ℝ)^4307 ≤ (13209529946079/100000000000000 : ℝ)^3283 := by
    have hnat : (2137462909 : ℕ)^4307*100000000000000^3283 ≤ 13209529946079^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137462909 10000000000 13209529946079 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676252607/5000000000 : ℝ), (2615899213/5000000000 : ℝ), (-2137462909/10000000000 : ℝ)] ![(2752779370179/6250000000000 : ℝ), (21373000057707/50000000000000 : ℝ), (13209529946079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676252607/5000000000 : ℝ)|^4307 ≤ (2752779370179/6250000000000 : ℝ)^3283
        have hw : |(2676252607/5000000000 : ℝ)|=(2676252607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615899213/5000000000 : ℝ)|^4307 ≤ (21373000057707/50000000000000 : ℝ)^3283
        have hw : |(2615899213/5000000000 : ℝ)|=(2615899213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2137462909/10000000000 : ℝ)|^4307 ≤ (13209529946079/100000000000000 : ℝ)^3283
        have hw : |(-2137462909/10000000000 : ℝ)|=(2137462909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s3_3 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324279331/10000000000 : ℝ)*x 0 + (4124452143/10000000000 : ℝ)*x 1 + (4533103927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324279331/10000000000 : ℝ)^4307 ≤ (16646451031997/50000000000000 : ℝ)^3283 := by
    have hnat : (4324279331 : ℕ)^4307*50000000000000^3283 ≤ 16646451031997^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324279331 10000000000 16646451031997 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4124452143/10000000000 : ℝ)^4307 ≤ (7822313768873/25000000000000 : ℝ)^3283 := by
    have hnat : (4124452143 : ℕ)^4307*25000000000000^3283 ≤ 7822313768873^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124452143 10000000000 7822313768873 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4533103927/10000000000 : ℝ)^4307 ≤ (35417842851747/100000000000000 : ℝ)^3283 := by
    have hnat : (4533103927 : ℕ)^4307*100000000000000^3283 ≤ 35417842851747^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533103927 10000000000 35417842851747 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324279331/10000000000 : ℝ), (4124452143/10000000000 : ℝ), (4533103927/10000000000 : ℝ)] ![(16646451031997/50000000000000 : ℝ), (7822313768873/25000000000000 : ℝ), (35417842851747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324279331/10000000000 : ℝ)|^4307 ≤ (16646451031997/50000000000000 : ℝ)^3283
        have hw : |(4324279331/10000000000 : ℝ)|=(4324279331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4124452143/10000000000 : ℝ)|^4307 ≤ (7822313768873/25000000000000 : ℝ)^3283
        have hw : |(4124452143/10000000000 : ℝ)|=(4124452143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4533103927/10000000000 : ℝ)|^4307 ≤ (35417842851747/100000000000000 : ℝ)^3283
        have hw : |(4533103927/10000000000 : ℝ)|=(4533103927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s3_4 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037970831/10000000000 : ℝ)*x 0 + (5232607777/10000000000 : ℝ)*x 1 + (5425718621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037970831/10000000000 : ℝ)^4307 ≤ (12408806495079/100000000000000 : ℝ)^3283 := by
    have hnat : (2037970831 : ℕ)^4307*100000000000000^3283 ≤ 12408806495079^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037970831 10000000000 12408806495079 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232607777/10000000000 : ℝ)^4307 ≤ (21377337821087/50000000000000 : ℝ)^3283 := by
    have hnat : (5232607777 : ℕ)^4307*50000000000000^3283 ≤ 21377337821087^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232607777 10000000000 21377337821087 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425718621/10000000000 : ℝ)^4307 ≤ (11209129463363/25000000000000 : ℝ)^3283 := by
    have hnat : (5425718621 : ℕ)^4307*25000000000000^3283 ≤ 11209129463363^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425718621 10000000000 11209129463363 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037970831/10000000000 : ℝ), (5232607777/10000000000 : ℝ), (5425718621/10000000000 : ℝ)] ![(12408806495079/100000000000000 : ℝ), (21377337821087/50000000000000 : ℝ), (11209129463363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037970831/10000000000 : ℝ)|^4307 ≤ (12408806495079/100000000000000 : ℝ)^3283
        have hw : |(-2037970831/10000000000 : ℝ)|=(2037970831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232607777/10000000000 : ℝ)|^4307 ≤ (21377337821087/50000000000000 : ℝ)^3283
        have hw : |(5232607777/10000000000 : ℝ)|=(5232607777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425718621/10000000000 : ℝ)|^4307 ≤ (11209129463363/25000000000000 : ℝ)^3283
        have hw : |(5425718621/10000000000 : ℝ)|=(5425718621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s3_5 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530231627/1000000000 : ℝ)*x 0 + (-971771329/5000000000 : ℝ)*x 1 + (1085143723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530231627/1000000000 : ℝ)^4307 ≤ (43503454795211/100000000000000 : ℝ)^3283 := by
    have hnat : (530231627 : ℕ)^4307*100000000000000^3283 ≤ 43503454795211^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530231627 1000000000 43503454795211 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971771329/5000000000 : ℝ)^4307 ≤ (5830013696177/50000000000000 : ℝ)^3283 := by
    have hnat : (971771329 : ℕ)^4307*50000000000000^3283 ≤ 5830013696177^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971771329 5000000000 5830013696177 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085143723/2000000000 : ℝ)^4307 ≤ (8967303557681/20000000000000 : ℝ)^3283 := by
    have hnat : (1085143723 : ℕ)^4307*20000000000000^3283 ≤ 8967303557681^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085143723 2000000000 8967303557681 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530231627/1000000000 : ℝ), (-971771329/5000000000 : ℝ), (1085143723/2000000000 : ℝ)] ![(43503454795211/100000000000000 : ℝ), (5830013696177/50000000000000 : ℝ), (8967303557681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530231627/1000000000 : ℝ)|^4307 ≤ (43503454795211/100000000000000 : ℝ)^3283
        have hw : |(530231627/1000000000 : ℝ)|=(530231627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-971771329/5000000000 : ℝ)|^4307 ≤ (5830013696177/50000000000000 : ℝ)^3283
        have hw : |(-971771329/5000000000 : ℝ)|=(971771329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085143723/2000000000 : ℝ)|^4307 ≤ (8967303557681/20000000000000 : ℝ)^3283
        have hw : |(1085143723/2000000000 : ℝ)|=(1085143723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s3_6 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651158023/5000000000 : ℝ)*x 0 + (542571877/1000000000 : ℝ)*x 1 + (-60735711/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651158023/5000000000 : ℝ)^4307 ≤ (43503452384139/100000000000000 : ℝ)^3283 := by
    have hnat : (2651158023 : ℕ)^4307*100000000000000^3283 ≤ 43503452384139^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651158023 5000000000 43503452384139 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542571877/1000000000 : ℝ)^4307 ≤ (8967303893759/20000000000000 : ℝ)^3283 := by
    have hnat : (542571877 : ℕ)^4307*20000000000000^3283 ≤ 8967303893759^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542571877 1000000000 8967303893759 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60735711/312500000 : ℝ)^4307 ≤ (11660028132193/100000000000000 : ℝ)^3283 := by
    have hnat : (60735711 : ℕ)^4307*100000000000000^3283 ≤ 11660028132193^3283*312500000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60735711 312500000 11660028132193 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651158023/5000000000 : ℝ), (542571877/1000000000 : ℝ), (-60735711/312500000 : ℝ)] ![(43503452384139/100000000000000 : ℝ), (8967303893759/20000000000000 : ℝ), (11660028132193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651158023/5000000000 : ℝ)|^4307 ≤ (43503452384139/100000000000000 : ℝ)^3283
        have hw : |(2651158023/5000000000 : ℝ)|=(2651158023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542571877/1000000000 : ℝ)|^4307 ≤ (8967303893759/20000000000000 : ℝ)^3283
        have hw : |(542571877/1000000000 : ℝ)|=(542571877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60735711/312500000 : ℝ)|^4307 ≤ (11660028132193/100000000000000 : ℝ)^3283
        have hw : |(-60735711/312500000 : ℝ)|=(60735711/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s3_7 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2162159471/5000000000 : ℝ)*x 0 + (4531405987/10000000000 : ℝ)*x 1 + (64471257/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162159471/5000000000 : ℝ)^4307 ≤ (33293302154577/100000000000000 : ℝ)^3283 := by
    have hnat : (2162159471 : ℕ)^4307*100000000000000^3283 ≤ 33293302154577^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162159471 5000000000 33293302154577 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4531405987/10000000000 : ℝ)^4307 ≤ (35400439720839/100000000000000 : ℝ)^3283 := by
    have hnat : (4531405987 : ℕ)^4307*100000000000000^3283 ≤ 35400439720839^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531405987 10000000000 35400439720839 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64471257/156250000 : ℝ)^4307 ≤ (31306258108803/100000000000000 : ℝ)^3283 := by
    have hnat : (64471257 : ℕ)^4307*100000000000000^3283 ≤ 31306258108803^3283*156250000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64471257 156250000 31306258108803 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162159471/5000000000 : ℝ), (4531405987/10000000000 : ℝ), (64471257/156250000 : ℝ)] ![(33293302154577/100000000000000 : ℝ), (35400439720839/100000000000000 : ℝ), (31306258108803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162159471/5000000000 : ℝ)|^4307 ≤ (33293302154577/100000000000000 : ℝ)^3283
        have hw : |(2162159471/5000000000 : ℝ)|=(2162159471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4531405987/10000000000 : ℝ)|^4307 ≤ (35400439720839/100000000000000 : ℝ)^3283
        have hw : |(4531405987/10000000000 : ℝ)|=(4531405987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64471257/156250000 : ℝ)|^4307 ≤ (31306258108803/100000000000000 : ℝ)^3283
        have hw : |(64471257/156250000 : ℝ)|=(64471257/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1347_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4021/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2471/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2721/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3001/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4021/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2471/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4021/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2471/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4021/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2471/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4021/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2471/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4021/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2471/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4021/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2471/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2471/25000 : ℝ) ^ (2153/512 : ℝ) ≤ (5937636914944783/100000000000000000000 : ℝ) := by
    have hpowers : (2471/25000 : ℝ)^2153 ≤ (5937636914944783/100000000000000000000 : ℝ)^512 := by
      have hnat : (2471 : ℕ)^2153*100000000000000000000^512 ≤ 5937636914944783^512*25000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2471 25000 5937636914944783 100000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2471/25000 : ℝ)) (X := (5937636914944783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hpowhi : (4021/25000 : ℝ) ^ (2153/512 : ℝ) ≤ (11501779808137483/25000000000000000000 : ℝ) := by
    have hpowers : (4021/25000 : ℝ)^2153 ≤ (11501779808137483/25000000000000000000 : ℝ)^512 := by
      have hnat : (4021 : ℕ)^2153*25000000000000000000^512 ≤ 11501779808137483^512*25000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4021 25000 11501779808137483 25000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4021/25000 : ℝ)) (X := (11501779808137483/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005937636914944783/50000000000000000000 : ℝ) ≤ (1000028239038811/1000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50005937636914944783/50000000000000000000 : ℝ)^512 ≤ (1000028239038811/1000000000000000 : ℝ)^2153 := by
      have hnat : (50005937636914944783 : ℕ)^512*1000000000000000^2153 ≤ 1000028239038811^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005937636914944783 50000000000000000000 1000028239038811 1000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000028239038811/1000000000000000 : ℝ)) (X := (50005937636914944783/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010388951229498943/20000000000000000000 : ℝ) ≤ (10001235041889451/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (20010388951229498943/20000000000000000000 : ℝ)^512 ≤ (10001235041889451/10000000000000000 : ℝ)^2153 := by
      have hnat : (20010388951229498943 : ℕ)^512*10000000000000000^2153 ≤ 10001235041889451^2153*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010388951229498943 20000000000000000000 10001235041889451 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001235041889451/10000000000000000 : ℝ)) (X := (20010388951229498943/20000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511501779808137483/12500000000000000000 : ℝ) ≤ (1250273461673849/1250000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (12511501779808137483/12500000000000000000 : ℝ)^512 ≤ (1250273461673849/1250000000000000 : ℝ)^2153 := by
      have hnat : (12511501779808137483 : ℕ)^512*1250000000000000^2153 ≤ 1250273461673849^2153*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511501779808137483 12500000000000000000 1250273461673849 1250000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250273461673849/1250000000000000 : ℝ)) (X := (12511501779808137483/12500000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5937636914944783/100000000000000000000 : ℝ) ≤ ((7747864850690971639/7750000000000000000 : ℝ)+2*(952651501341/620000000000000 : ℝ)*(2471/25000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (7747864850690971639/7750000000000000000 : ℝ)+2*(952651501341/620000000000000 : ℝ)*(2471/25000 : ℝ)=(1000028239038811/1000000000000000 : ℝ) by norm_num, show 1+2*(5937636914944783/100000000000000000000 : ℝ)=(50005937636914944783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11501779808137483/25000000000000000000 : ℝ)+(5937636914944783/100000000000000000000 : ℝ) ≤ ((7747864850690971639/7750000000000000000 : ℝ)+(952651501341/620000000000000 : ℝ)*((4021/25000 : ℝ)+(2471/25000 : ℝ)))^(2153/512 : ℝ) := by
    rw [show (7747864850690971639/7750000000000000000 : ℝ)+(952651501341/620000000000000 : ℝ)*((4021/25000 : ℝ)+(2471/25000 : ℝ))=(10001235041889451/10000000000000000 : ℝ) by norm_num, show 1+(11501779808137483/25000000000000000000 : ℝ)+(5937636914944783/100000000000000000000 : ℝ)=(20010388951229498943/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11501779808137483/25000000000000000000 : ℝ) ≤ ((7747864850690971639/7750000000000000000 : ℝ)+2*(952651501341/620000000000000 : ℝ)*(4021/25000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (7747864850690971639/7750000000000000000 : ℝ)+2*(952651501341/620000000000000 : ℝ)*(4021/25000 : ℝ)=(1250273461673849/1250000000000000 : ℝ) by norm_num, show 1+2*(11501779808137483/25000000000000000000 : ℝ)=(12511501779808137483/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7747864850690971639/7750000000000000000 : ℝ)*(X 1 0+X 2 0)+(952651501341/620000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (2471/25000 : ℝ)) (hi := (4021/25000 : ℝ)) (c := (7747864850690971639/7750000000000000000 : ℝ)) (alpha := (952651501341/620000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7747864850690971639/7750000000000000000 : ℝ)*(X 0 1+X 2 1)+(952651501341/620000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (2471/25000 : ℝ)) (hi := (4021/25000 : ℝ)) (c := (7747864850690971639/7750000000000000000 : ℝ)) (alpha := (952651501341/620000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7747864850690971639/7750000000000000000 : ℝ)*(X 0 2+X 1 2)+(952651501341/620000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (2471/25000 : ℝ)) (hi := (4021/25000 : ℝ)) (c := (7747864850690971639/7750000000000000000 : ℝ)) (alpha := (952651501341/620000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2037951803/10000000000 : ℝ)*X 0 0+(678316563/1250000000 : ℝ)*X 0 1+(2615899391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352505171/10000000000 : ℝ)*X 1 0+(-213746269/1000000000 : ℝ)*X 1 1+(1046359727/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676252607/5000000000 : ℝ)*X 2 0+(2615899213/5000000000 : ℝ)*X 2 1+(-2137462909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324279331/10000000000 : ℝ)*X 0 0+(4124452143/10000000000 : ℝ)*X 0 1+(4533103927/10000000000 : ℝ)*X 0 2+(4324279331/10000000000 : ℝ)*X 1 0+(4124452143/10000000000 : ℝ)*X 1 1+(4533103927/10000000000 : ℝ)*X 1 2+(4324279331/10000000000 : ℝ)*X 2 0+(4124452143/10000000000 : ℝ)*X 2 1+(4533103927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2037970831/10000000000 : ℝ)*X 0 0+(5232607777/10000000000 : ℝ)*X 0 1+(5425718621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530231627/1000000000 : ℝ)*X 1 0+(-971771329/5000000000 : ℝ)*X 1 1+(1085143723/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651158023/5000000000 : ℝ)*X 2 0+(542571877/1000000000 : ℝ)*X 2 1+(-60735711/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162159471/5000000000 : ℝ)*X 0 0+(4531405987/10000000000 : ℝ)*X 0 1+(64471257/156250000 : ℝ)*X 0 2+(2162159471/5000000000 : ℝ)*X 1 0+(4531405987/10000000000 : ℝ)*X 1 1+(64471257/156250000 : ℝ)*X 1 2+(2162159471/5000000000 : ℝ)*X 2 0+(4531405987/10000000000 : ℝ)*X 2 1+(64471257/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10231622505660184693628319/3125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174115537/25000000000000 : ℝ)*(base19) + (16593871/2000000000000 : ℝ)*(base23) + (5837367/20000000000000 : ℝ)*(lower2) + (158073291/100000000000000 : ℝ)*(upper3) + (9802189/12500000000000 : ℝ)*(lower4) + (1895578763254167/50000000000000 : ℝ)*(major0) + (1895578763254167/50000000000000 : ℝ)*(major1) + (1895578763254167/50000000000000 : ℝ)*(major2) + (2567614159535991/50000000000000 : ℝ)*(sp0) + (5135232703366631/100000000000000 : ℝ)*(sp1) + (5135232570135229/100000000000000 : ℝ)*(sp2) + (305884428250171/12500000000000 : ℝ)*(sp3) + (5080756797/100000000000000 : ℝ)*(sp4) + (611804921/10000000000000 : ℝ)*(sp7) + (1223540772025289/50000000000000 : ℝ)*(f.failure) + (5135233399828779/100000000000000 : ℝ)*(f.sum) + (4418122634663/500000000000000000000000000 : ℝ)*base66 + (35977238509438477/12500000000000000000000000000000 : ℝ)*base68 + (89258438334438477/12500000000000000000000000000000 : ℝ)*base70 + (14168456015561523/12500000000000000000000000000000 : ℝ)*base71 + (494655499163/500000000000000000000000000 : ℝ)*base74 + (150723511134438477/12500000000000000000000000000000 : ℝ)*base76 + (15471982796938477/12500000000000000000000000000000 : ℝ)*base78 + (76262692971938477/12500000000000000000000000000000 : ℝ)*base80 + (837123225337/500000000000000000000000000 : ℝ)*base81 + (85099/625000000000000000000 : ℝ)*base90 + (85099/625000000000000000000 : ℝ)*base92 + (85099/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1870410108531692866510778751/193750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1818565521/100000000000000 : ℝ)*(base19) + (68806059/4000000000000 : ℝ)*(base23) + (2284643/1250000000000 : ℝ)*(upper3) + (18200181/25000000000000 : ℝ)*(lower4) + (27271179/12500000000000 : ℝ)*(upper5) + (3823004845404247/100000000000000 : ℝ)*(major0) + (3823004845404247/100000000000000 : ℝ)*(major1) + (3823004845404247/100000000000000 : ℝ)*(major2) + (16655957199/50000000000000 : ℝ)*(sp1) + (31521015321/100000000000000 : ℝ)*(sp2) + (5178371310036387/100000000000000 : ℝ)*(sp4) + (5178336179556469/100000000000000 : ℝ)*(sp5) + (5178338068869591/100000000000000 : ℝ)*(sp6) + (1233819029490557/50000000000000 : ℝ)*(sp7) + (1233819029490557/50000000000000 : ℝ)*(f.failure) + (5178371310036387/100000000000000 : ℝ)*(f.sum) + (76197760074227/31000000000000000000000000000 : ℝ)*base65 + (409041734067511667/775000000000000000000000000000000 : ℝ)*base68 + (13308977374882488333/775000000000000000000000000000000 : ℝ)*base69 + (6655429800207488333/775000000000000000000000000000000 : ℝ)*base71 + (98751685580773/31000000000000000000000000000 : ℝ)*base74 + (2569992375432488333/775000000000000000000000000000000 : ℝ)*base75 + (3942667701407488333/775000000000000000000000000000000 : ℝ)*base77 + (8789103025257488333/775000000000000000000000000000000 : ℝ)*base79 + (62233436214227/31000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1359913/625000000000000000000 : ℝ)*base89 + (1359913/625000000000000000000 : ℝ)*base91 + (1359913/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1347_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4021/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2471/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3001/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1347_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1347_s4_0 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1019684681/5000000000 : ℝ)*x 0 + (1353730087/2500000000 : ℝ)*x 1 + (5242480227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019684681/5000000000 : ℝ)^4307 ≤ (12419979104177/100000000000000 : ℝ)^3283 := by
    have hnat : (1019684681 : ℕ)^4307*100000000000000^3283 ≤ 12419979104177^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019684681 5000000000 12419979104177 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353730087/2500000000 : ℝ)^4307 ≤ (8943897526681/20000000000000 : ℝ)^3283 := by
    have hnat : (1353730087 : ℕ)^4307*20000000000000^3283 ≤ 8943897526681^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353730087 2500000000 8943897526681 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242480227/10000000000 : ℝ)^4307 ≤ (42860533250977/100000000000000 : ℝ)^3283 := by
    have hnat : (5242480227 : ℕ)^4307*100000000000000^3283 ≤ 42860533250977^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242480227 10000000000 42860533250977 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1019684681/5000000000 : ℝ), (1353730087/2500000000 : ℝ), (5242480227/10000000000 : ℝ)] ![(12419979104177/100000000000000 : ℝ), (8943897526681/20000000000000 : ℝ), (42860533250977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1019684681/5000000000 : ℝ)|^4307 ≤ (12419979104177/100000000000000 : ℝ)^3283
        have hw : |(-1019684681/5000000000 : ℝ)|=(1019684681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353730087/2500000000 : ℝ)|^4307 ≤ (8943897526681/20000000000000 : ℝ)^3283
        have hw : |(1353730087/2500000000 : ℝ)|=(1353730087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242480227/10000000000 : ℝ)|^4307 ≤ (42860533250977/100000000000000 : ℝ)^3283
        have hw : |(5242480227/10000000000 : ℝ)|=(5242480227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s4_1 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069908769/2000000000 : ℝ)*x 0 + (-106363581/500000000 : ℝ)*x 1 + (2621240053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069908769/2000000000 : ℝ)^4307 ≤ (44012503552711/100000000000000 : ℝ)^3283 := by
    have hnat : (1069908769 : ℕ)^4307*100000000000000^3283 ≤ 44012503552711^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069908769 2000000000 44012503552711 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106363581/500000000 : ℝ)^4307 ≤ (13126964472839/100000000000000 : ℝ)^3283 := by
    have hnat : (106363581 : ℕ)^4307*100000000000000^3283 ≤ 13126964472839^3283*500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106363581 500000000 13126964472839 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621240053/5000000000 : ℝ)^4307 ≤ (4286053195317/10000000000000 : ℝ)^3283 := by
    have hnat : (2621240053 : ℕ)^4307*10000000000000^3283 ≤ 4286053195317^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621240053 5000000000 4286053195317 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069908769/2000000000 : ℝ), (-106363581/500000000 : ℝ), (2621240053/5000000000 : ℝ)] ![(44012503552711/100000000000000 : ℝ), (13126964472839/100000000000000 : ℝ), (4286053195317/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069908769/2000000000 : ℝ)|^4307 ≤ (44012503552711/100000000000000 : ℝ)^3283
        have hw : |(1069908769/2000000000 : ℝ)|=(1069908769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106363581/500000000 : ℝ)|^4307 ≤ (13126964472839/100000000000000 : ℝ)^3283
        have hw : |(-106363581/500000000 : ℝ)|=(106363581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621240053/5000000000 : ℝ)|^4307 ≤ (4286053195317/10000000000000 : ℝ)^3283
        have hw : |(2621240053/5000000000 : ℝ)|=(2621240053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s4_2 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349544143/10000000000 : ℝ)*x 0 + (1310619939/2500000000 : ℝ)*x 1 + (-1063635843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349544143/10000000000 : ℝ)^4307 ≤ (22006253384591/50000000000000 : ℝ)^3283 := by
    have hnat : (5349544143 : ℕ)^4307*50000000000000^3283 ≤ 22006253384591^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349544143 10000000000 22006253384591 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310619939/2500000000 : ℝ)^4307 ≤ (21430264099591/50000000000000 : ℝ)^3283 := by
    have hnat : (1310619939 : ℕ)^4307*50000000000000^3283 ≤ 21430264099591^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310619939 2500000000 21430264099591 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063635843/5000000000 : ℝ)^4307 ≤ (2625393001429/20000000000000 : ℝ)^3283 := by
    have hnat : (1063635843 : ℕ)^4307*20000000000000^3283 ≤ 2625393001429^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063635843 5000000000 2625393001429 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349544143/10000000000 : ℝ), (1310619939/2500000000 : ℝ), (-1063635843/5000000000 : ℝ)] ![(22006253384591/50000000000000 : ℝ), (21430264099591/50000000000000 : ℝ), (2625393001429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349544143/10000000000 : ℝ)|^4307 ≤ (22006253384591/50000000000000 : ℝ)^3283
        have hw : |(5349544143/10000000000 : ℝ)|=(5349544143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310619939/2500000000 : ℝ)|^4307 ≤ (21430264099591/50000000000000 : ℝ)^3283
        have hw : |(1310619939/2500000000 : ℝ)|=(1310619939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1063635843/5000000000 : ℝ)|^4307 ≤ (2625393001429/20000000000000 : ℝ)^3283
        have hw : |(-1063635843/5000000000 : ℝ)|=(1063635843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s4_3 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (43251423/100000000 : ℝ)*x 0 + (33181897/80000000 : ℝ)*x 1 + (901921157/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43251423/100000000 : ℝ)^4307 ≤ (33301618734167/100000000000000 : ℝ)^3283 := by
    have hnat : (43251423 : ℕ)^4307*100000000000000^3283 ≤ 33301618734167^3283*100000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43251423 100000000 33301618734167 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33181897/80000000 : ℝ)^4307 ≤ (7880300760167/25000000000000 : ℝ)^3283 := by
    have hnat : (33181897 : ℕ)^4307*25000000000000^3283 ≤ 7880300760167^3283*80000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33181897 80000000 7880300760167 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901921157/2000000000 : ℝ)^4307 ≤ (8794294552221/25000000000000 : ℝ)^3283 := by
    have hnat : (901921157 : ℕ)^4307*25000000000000^3283 ≤ 8794294552221^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901921157 2000000000 8794294552221 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43251423/100000000 : ℝ), (33181897/80000000 : ℝ), (901921157/2000000000 : ℝ)] ![(33301618734167/100000000000000 : ℝ), (7880300760167/25000000000000 : ℝ), (8794294552221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43251423/100000000 : ℝ)|^4307 ≤ (33301618734167/100000000000000 : ℝ)^3283
        have hw : |(43251423/100000000 : ℝ)|=(43251423/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33181897/80000000 : ℝ)|^4307 ≤ (7880300760167/25000000000000 : ℝ)^3283
        have hw : |(33181897/80000000 : ℝ)|=(33181897/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901921157/2000000000 : ℝ)|^4307 ≤ (8794294552221/25000000000000 : ℝ)^3283
        have hw : |(901921157/2000000000 : ℝ)|=(901921157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s4_4 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2039382787/10000000000 : ℝ)*x 0 + (524311491/1000000000 : ℝ)*x 1 + (1353570529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2039382787/10000000000 : ℝ)^4307 ≤ (12420086365637/100000000000000 : ℝ)^3283 := by
    have hnat : (2039382787 : ℕ)^4307*100000000000000^3283 ≤ 12420086365637^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039382787 10000000000 12420086365637 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524311491/1000000000 : ℝ)^4307 ≤ (42867340785043/100000000000000 : ℝ)^3283 := by
    have hnat : (524311491 : ℕ)^4307*100000000000000^3283 ≤ 42867340785043^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524311491 1000000000 42867340785043 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353570529/2500000000 : ℝ)^4307 ≤ (22356286419059/50000000000000 : ℝ)^3283 := by
    have hnat : (1353570529 : ℕ)^4307*50000000000000^3283 ≤ 22356286419059^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353570529 2500000000 22356286419059 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2039382787/10000000000 : ℝ), (524311491/1000000000 : ℝ), (1353570529/2500000000 : ℝ)] ![(12420086365637/100000000000000 : ℝ), (42867340785043/100000000000000 : ℝ), (22356286419059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2039382787/10000000000 : ℝ)|^4307 ≤ (12420086365637/100000000000000 : ℝ)^3283
        have hw : |(-2039382787/10000000000 : ℝ)|=(2039382787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524311491/1000000000 : ℝ)|^4307 ≤ (42867340785043/100000000000000 : ℝ)^3283
        have hw : |(524311491/1000000000 : ℝ)|=(524311491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353570529/2500000000 : ℝ)|^4307 ≤ (22356286419059/50000000000000 : ℝ)^3283
        have hw : |(1353570529/2500000000 : ℝ)|=(1353570529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s4_5 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663137713/1250000000 : ℝ)*x 0 + (-9777347/50000000 : ℝ)*x 1 + (1082856427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663137713/1250000000 : ℝ)^4307 ≤ (43533438863261/100000000000000 : ℝ)^3283 := by
    have hnat : (663137713 : ℕ)^4307*100000000000000^3283 ≤ 43533438863261^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663137713 1250000000 43533438863261 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9777347/50000000 : ℝ)^4307 ≤ (2938497018543/25000000000000 : ℝ)^3283 := by
    have hnat : (9777347 : ℕ)^4307*25000000000000^3283 ≤ 2938497018543^3283*50000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9777347 50000000 2938497018543 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082856427/2000000000 : ℝ)^4307 ≤ (22356286521983/50000000000000 : ℝ)^3283 := by
    have hnat : (1082856427 : ℕ)^4307*50000000000000^3283 ≤ 22356286521983^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082856427 2000000000 22356286521983 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663137713/1250000000 : ℝ), (-9777347/50000000 : ℝ), (1082856427/2000000000 : ℝ)] ![(43533438863261/100000000000000 : ℝ), (2938497018543/25000000000000 : ℝ), (22356286521983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663137713/1250000000 : ℝ)|^4307 ≤ (43533438863261/100000000000000 : ℝ)^3283
        have hw : |(663137713/1250000000 : ℝ)|=(663137713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9777347/50000000 : ℝ)|^4307 ≤ (2938497018543/25000000000000 : ℝ)^3283
        have hw : |(-9777347/50000000 : ℝ)|=(9777347/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082856427/2000000000 : ℝ)|^4307 ≤ (22356286521983/50000000000000 : ℝ)^3283
        have hw : |(1082856427/2000000000 : ℝ)|=(1082856427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s4_6 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652550911/5000000000 : ℝ)*x 0 + (270714103/500000000 : ℝ)*x 1 + (-1955469343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652550911/5000000000 : ℝ)^4307 ≤ (10883360033397/25000000000000 : ℝ)^3283 := by
    have hnat : (2652550911 : ℕ)^4307*25000000000000^3283 ≤ 10883360033397^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652550911 5000000000 10883360033397 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270714103/500000000 : ℝ)^4307 ≤ (2794535764463/6250000000000 : ℝ)^3283 := by
    have hnat : (270714103 : ℕ)^4307*6250000000000^3283 ≤ 2794535764463^3283*500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270714103 500000000 2794535764463 6250000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1955469343/10000000000 : ℝ)^4307 ≤ (1175398762469/10000000000000 : ℝ)^3283 := by
    have hnat : (1955469343 : ℕ)^4307*10000000000000^3283 ≤ 1175398762469^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955469343 10000000000 1175398762469 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652550911/5000000000 : ℝ), (270714103/500000000 : ℝ), (-1955469343/10000000000 : ℝ)] ![(10883360033397/25000000000000 : ℝ), (2794535764463/6250000000000 : ℝ), (1175398762469/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652550911/5000000000 : ℝ)|^4307 ≤ (10883360033397/25000000000000 : ℝ)^3283
        have hw : |(2652550911/5000000000 : ℝ)|=(2652550911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270714103/500000000 : ℝ)|^4307 ≤ (2794535764463/6250000000000 : ℝ)^3283
        have hw : |(270714103/500000000 : ℝ)|=(270714103/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1955469343/10000000000 : ℝ)|^4307 ≤ (1175398762469/10000000000000 : ℝ)^3283
        have hw : |(-1955469343/10000000000 : ℝ)|=(1955469343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s4_7 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325170179/10000000000 : ℝ)*x 0 + (901654667/2000000000 : ℝ)*x 1 + (207453821/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325170179/10000000000 : ℝ)^4307 ≤ (33301900343187/100000000000000 : ℝ)^3283 := by
    have hnat : (4325170179 : ℕ)^4307*100000000000000^3283 ≤ 33301900343187^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325170179 10000000000 33301900343187 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901654667/2000000000 : ℝ)^4307 ≤ (17581771570317/50000000000000 : ℝ)^3283 := by
    have hnat : (901654667 : ℕ)^4307*50000000000000^3283 ≤ 17581771570317^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901654667 2000000000 17581771570317 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207453821/500000000 : ℝ)^4307 ≤ (3153455649621/10000000000000 : ℝ)^3283 := by
    have hnat : (207453821 : ℕ)^4307*10000000000000^3283 ≤ 3153455649621^3283*500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207453821 500000000 3153455649621 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325170179/10000000000 : ℝ), (901654667/2000000000 : ℝ), (207453821/500000000 : ℝ)] ![(33301900343187/100000000000000 : ℝ), (17581771570317/50000000000000 : ℝ), (3153455649621/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325170179/10000000000 : ℝ)|^4307 ≤ (33301900343187/100000000000000 : ℝ)^3283
        have hw : |(4325170179/10000000000 : ℝ)|=(4325170179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901654667/2000000000 : ℝ)|^4307 ≤ (17581771570317/50000000000000 : ℝ)^3283
        have hw : |(901654667/2000000000 : ℝ)|=(901654667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207453821/500000000 : ℝ)|^4307 ≤ (3153455649621/10000000000000 : ℝ)^3283
        have hw : |(207453821/500000000 : ℝ)|=(207453821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1347_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3001/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1389/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3001/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2721/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3001/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2721/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3001/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2721/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3001/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2721/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3001/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2721/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3001/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2721/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2721/25000 : ℝ) ^ (2153/512 : ℝ) ≤ (4452362693831553/50000000000000000000 : ℝ) := by
    have hpowers : (2721/25000 : ℝ)^2153 ≤ (4452362693831553/50000000000000000000 : ℝ)^512 := by
      have hnat : (2721 : ℕ)^2153*50000000000000000000^512 ≤ 4452362693831553^512*25000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2721 25000 4452362693831553 50000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2721/25000 : ℝ)) (X := (4452362693831553/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3001/20000 : ℝ) ^ (2153/512 : ℝ) ≤ (17178214713751841/50000000000000000000 : ℝ) := by
    have hpowers : (3001/20000 : ℝ)^2153 ≤ (17178214713751841/50000000000000000000 : ℝ)^512 := by
      have hnat : (3001 : ℕ)^2153*50000000000000000000^512 ≤ 17178214713751841^512*20000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3001 20000 17178214713751841 50000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3001/20000 : ℝ)) (X := (17178214713751841/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004452362693831553/25000000000000000000 : ℝ) ≤ (1250052936716111/1250000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (25004452362693831553/25000000000000000000 : ℝ)^512 ≤ (1250052936716111/1250000000000000 : ℝ)^2153 := by
      have hnat : (25004452362693831553 : ℕ)^512*1250000000000000^2153 ≤ 1250052936716111^2153*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004452362693831553 25000000000000000000 1250052936716111 1250000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250052936716111/1250000000000000 : ℝ)) (X := (25004452362693831553/25000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010815288703791697/25000000000000000000 : ℝ) ≤ (10001028614047637/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (25010815288703791697/25000000000000000000 : ℝ)^512 ≤ (10001028614047637/10000000000000000 : ℝ)^2153 := by
      have hnat : (25010815288703791697 : ℕ)^512*10000000000000000^2153 ≤ 10001028614047637^2153*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010815288703791697 25000000000000000000 10001028614047637 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001028614047637/10000000000000000 : ℝ)) (X := (25010815288703791697/25000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017178214713751841/25000000000000000000 : ℝ) ≤ (5000816867183193/5000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (25017178214713751841/25000000000000000000 : ℝ)^512 ≤ (5000816867183193/5000000000000000 : ℝ)^2153 := by
      have hnat : (25017178214713751841 : ℕ)^512*5000000000000000^2153 ≤ 5000816867183193^2153*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017178214713751841 25000000000000000000 5000816867183193 5000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000816867183193/5000000000000000 : ℝ)) (X := (25017178214713751841/25000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4452362693831553/50000000000000000000 : ℝ) ≤ ((2574910809909888701/2575625000000000000 : ℝ)+2*(605120318749/412100000000000 : ℝ)*(2721/25000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (2574910809909888701/2575625000000000000 : ℝ)+2*(605120318749/412100000000000 : ℝ)*(2721/25000 : ℝ)=(1250052936716111/1250000000000000 : ℝ) by norm_num, show 1+2*(4452362693831553/50000000000000000000 : ℝ)=(25004452362693831553/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17178214713751841/50000000000000000000 : ℝ)+(4452362693831553/50000000000000000000 : ℝ) ≤ ((2574910809909888701/2575625000000000000 : ℝ)+(605120318749/412100000000000 : ℝ)*((3001/20000 : ℝ)+(2721/25000 : ℝ)))^(2153/512 : ℝ) := by
    rw [show (2574910809909888701/2575625000000000000 : ℝ)+(605120318749/412100000000000 : ℝ)*((3001/20000 : ℝ)+(2721/25000 : ℝ))=(10001028614047637/10000000000000000 : ℝ) by norm_num, show 1+(17178214713751841/50000000000000000000 : ℝ)+(4452362693831553/50000000000000000000 : ℝ)=(25010815288703791697/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17178214713751841/50000000000000000000 : ℝ) ≤ ((2574910809909888701/2575625000000000000 : ℝ)+2*(605120318749/412100000000000 : ℝ)*(3001/20000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (2574910809909888701/2575625000000000000 : ℝ)+2*(605120318749/412100000000000 : ℝ)*(3001/20000 : ℝ)=(5000816867183193/5000000000000000 : ℝ) by norm_num, show 1+2*(17178214713751841/50000000000000000000 : ℝ)=(25017178214713751841/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2574910809909888701/2575625000000000000 : ℝ)*(X 1 0+X 2 0)+(605120318749/412100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (3001/20000 : ℝ)) (c := (2574910809909888701/2575625000000000000 : ℝ)) (alpha := (605120318749/412100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2574910809909888701/2575625000000000000 : ℝ)*(X 0 1+X 2 1)+(605120318749/412100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (3001/20000 : ℝ)) (c := (2574910809909888701/2575625000000000000 : ℝ)) (alpha := (605120318749/412100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2574910809909888701/2575625000000000000 : ℝ)*(X 0 2+X 1 2)+(605120318749/412100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (3001/20000 : ℝ)) (c := (2574910809909888701/2575625000000000000 : ℝ)) (alpha := (605120318749/412100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1019684681/5000000000 : ℝ)*X 0 0+(1353730087/2500000000 : ℝ)*X 0 1+(5242480227/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069908769/2000000000 : ℝ)*X 1 0+(-106363581/500000000 : ℝ)*X 1 1+(2621240053/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349544143/10000000000 : ℝ)*X 2 0+(1310619939/2500000000 : ℝ)*X 2 1+(-1063635843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((43251423/100000000 : ℝ)*X 0 0+(33181897/80000000 : ℝ)*X 0 1+(901921157/2000000000 : ℝ)*X 0 2+(43251423/100000000 : ℝ)*X 1 0+(33181897/80000000 : ℝ)*X 1 1+(901921157/2000000000 : ℝ)*X 1 2+(43251423/100000000 : ℝ)*X 2 0+(33181897/80000000 : ℝ)*X 2 1+(901921157/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2039382787/10000000000 : ℝ)*X 0 0+(524311491/1000000000 : ℝ)*X 0 1+(1353570529/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663137713/1250000000 : ℝ)*X 1 0+(-9777347/50000000 : ℝ)*X 1 1+(1082856427/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652550911/5000000000 : ℝ)*X 2 0+(270714103/500000000 : ℝ)*X 2 1+(-1955469343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325170179/10000000000 : ℝ)*X 0 0+(901654667/2000000000 : ℝ)*X 0 1+(207453821/500000000 : ℝ)*X 0 2+(4325170179/10000000000 : ℝ)*X 1 0+(901654667/2000000000 : ℝ)*X 1 1+(207453821/500000000 : ℝ)*X 1 2+(4325170179/10000000000 : ℝ)*X 2 0+(901654667/2000000000 : ℝ)*X 2 1+(207453821/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (217244539292827639534639833/32195312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (73745587/50000000000000 : ℝ)*(base19) + (43567401/12500000000000 : ℝ)*(base23) + (41229793/50000000000000 : ℝ)*(lower2) + (36326177/100000000000000 : ℝ)*(lower4) + (58929517/100000000000000 : ℝ)*(upper5) + (1070318271375143/25000000000000 : ℝ)*(major0) + (1070318271375143/25000000000000 : ℝ)*(major1) + (4281273085500573/100000000000000 : ℝ)*(major2) + (57991091119933/1000000000000 : ℝ)*(sp0) + (2899554482251063/50000000000000 : ℝ)*(sp1) + (5799104459335099/100000000000000 : ℝ)*(sp2) + (690858730322579/25000000000000 : ℝ)*(sp3) + (2152059497/50000000000000 : ℝ)*(sp6) + (478198487/25000000000000 : ℝ)*(sp7) + (552687366816853/20000000000000 : ℝ)*(f.failure) + (57991091119933/1000000000000 : ℝ)*(f.sum) + (26340142814343/8242000000000000000000000000 : ℝ)*base66 + (421704215734153389/128781250000000000000000000000000 : ℝ)*base68 + (114453380903099327/257562500000000000000000000000000 : ℝ)*base70 + (202767266900465889/128781250000000000000000000000000 : ℝ)*base72 + (42723489575201/8242000000000000000000000000 : ℝ)*base73 + (1960669406535900673/257562500000000000000000000000000 : ℝ)*base75 + (284292027308768783/16097656250000000000000000000000 : ℝ)*base78 + (1115683265883309507/64390625000000000000000000000000 : ℝ)*base80 + (5163568084013/1287812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1493777/250000000000000000000 : ℝ)*base89 + (1493777/250000000000000000000 : ℝ)*base91 + (1006223/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30370845985120128137120853/4953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (736073353/100000000000000 : ℝ)*(base19) + (97536423/10000000000000 : ℝ)*(base23) + (74043147/50000000000000 : ℝ)*(upper3) + (668261/2000000000000 : ℝ)*(lower4) + (574189/625000000000 : ℝ)*(upper5) + (1078278580710097/25000000000000 : ℝ)*(major0) + (1078278580710097/25000000000000 : ℝ)*(major1) + (1078278580710097/25000000000000 : ℝ)*(major2) + (5836846997/50000000000000 : ℝ)*(sp1) + (17207737593/100000000000000 : ℝ)*(sp2) + (11684478035489/200000000000 : ℝ)*(sp4) + (91284790749643/1562500000000 : ℝ)*(sp5) + (1460555208660669/25000000000000 : ℝ)*(sp6) + (2783989423547821/100000000000000 : ℝ)*(sp7) + (2783989423547821/100000000000000 : ℝ)*(f.failure) + (11684478035489/200000000000 : ℝ)*(f.sum) + (4942654766391/1585000000000000000000000000 : ℝ)*base66 + (8466674258561089/1238281250000000000000000000000 : ℝ)*base68 + (21363497766197481/4953125000000000000000000000000 : ℝ)*base70 + (11903241706606553/2476562500000000000000000000000 : ℝ)*base72 + (140335377551/1585000000000000000000000000 : ℝ)*base74 + (54208169332259981/4953125000000000000000000000000 : ℝ)*base76 + (10884265306146269/4953125000000000000000000000000 : ℝ)*base77 + (5793178268257107/619140625000000000000000000000 : ℝ)*base80 + (1520020651017/792500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (929911/1250000000000000000000 : ℝ)*base90 + (929911/1250000000000000000000 : ℝ)*base92 + (929911/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1347_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3001/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1347_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1347_s5_0 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-254951731/1250000000 : ℝ)*x 0 + (2706409577/5000000000 : ℝ)*x 1 + (41955363/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (254951731/1250000000 : ℝ)^4307 ≤ (2484386500741/20000000000000 : ℝ)^3283 := by
    have hnat : (254951731 : ℕ)^4307*20000000000000^3283 ≤ 2484386500741^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254951731 1250000000 2484386500741 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706409577/5000000000 : ℝ)^4307 ≤ (44696723632073/100000000000000 : ℝ)^3283 := by
    have hnat : (2706409577 : ℕ)^4307*100000000000000^3283 ≤ 44696723632073^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706409577 5000000000 44696723632073 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41955363/80000000 : ℝ)^4307 ≤ (42881343854789/100000000000000 : ℝ)^3283 := by
    have hnat : (41955363 : ℕ)^4307*100000000000000^3283 ≤ 42881343854789^3283*80000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41955363 80000000 42881343854789 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-254951731/1250000000 : ℝ), (2706409577/5000000000 : ℝ), (41955363/80000000 : ℝ)] ![(2484386500741/20000000000000 : ℝ), (44696723632073/100000000000000 : ℝ), (42881343854789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-254951731/1250000000 : ℝ)|^4307 ≤ (2484386500741/20000000000000 : ℝ)^3283
        have hw : |(-254951731/1250000000 : ℝ)|=(254951731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706409577/5000000000 : ℝ)|^4307 ≤ (44696723632073/100000000000000 : ℝ)^3283
        have hw : |(2706409577/5000000000 : ℝ)|=(2706409577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41955363/80000000 : ℝ)|^4307 ≤ (42881343854789/100000000000000 : ℝ)^3283
        have hw : |(41955363/80000000 : ℝ)|=(41955363/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s5_1 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337251633/2500000000 : ℝ)*x 0 + (-265677123/1250000000 : ℝ)*x 1 + (104888407/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337251633/2500000000 : ℝ)^4307 ≤ (44006704142139/100000000000000 : ℝ)^3283 := by
    have hnat : (1337251633 : ℕ)^4307*100000000000000^3283 ≤ 44006704142139^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337251633 2500000000 44006704142139 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265677123/1250000000 : ℝ)^4307 ≤ (13111952251033/100000000000000 : ℝ)^3283 := by
    have hnat : (265677123 : ℕ)^4307*100000000000000^3283 ≤ 13111952251033^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265677123 1250000000 13111952251033 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104888407/200000000 : ℝ)^4307 ≤ (5360167948327/12500000000000 : ℝ)^3283 := by
    have hnat : (104888407 : ℕ)^4307*12500000000000^3283 ≤ 5360167948327^3283*200000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104888407 200000000 5360167948327 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337251633/2500000000 : ℝ), (-265677123/1250000000 : ℝ), (104888407/200000000 : ℝ)] ![(44006704142139/100000000000000 : ℝ), (13111952251033/100000000000000 : ℝ), (5360167948327/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337251633/2500000000 : ℝ)|^4307 ≤ (44006704142139/100000000000000 : ℝ)^3283
        have hw : |(1337251633/2500000000 : ℝ)|=(1337251633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265677123/1250000000 : ℝ)|^4307 ≤ (13111952251033/100000000000000 : ℝ)^3283
        have hw : |(-265677123/1250000000 : ℝ)|=(265677123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104888407/200000000 : ℝ)|^4307 ≤ (5360167948327/12500000000000 : ℝ)^3283
        have hw : |(104888407/200000000 : ℝ)|=(104888407/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s5_2 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349006509/10000000000 : ℝ)*x 0 + (2622210197/5000000000 : ℝ)*x 1 + (-531354239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349006509/10000000000 : ℝ)^4307 ≤ (5500837986737/12500000000000 : ℝ)^3283 := by
    have hnat : (5349006509 : ℕ)^4307*12500000000000^3283 ≤ 5500837986737^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349006509 10000000000 5500837986737 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622210197/5000000000 : ℝ)^4307 ≤ (42881344058601/100000000000000 : ℝ)^3283 := by
    have hnat : (2622210197 : ℕ)^4307*100000000000000^3283 ≤ 42881344058601^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622210197 5000000000 42881344058601 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531354239/2500000000 : ℝ)^4307 ≤ (655597601221/5000000000000 : ℝ)^3283 := by
    have hnat : (531354239 : ℕ)^4307*5000000000000^3283 ≤ 655597601221^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531354239 2500000000 655597601221 5000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349006509/10000000000 : ℝ), (2622210197/5000000000 : ℝ), (-531354239/2500000000 : ℝ)] ![(5500837986737/12500000000000 : ℝ), (42881344058601/100000000000000 : ℝ), (655597601221/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349006509/10000000000 : ℝ)|^4307 ≤ (5500837986737/12500000000000 : ℝ)^3283
        have hw : |(5349006509/10000000000 : ℝ)|=(5349006509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622210197/5000000000 : ℝ)|^4307 ≤ (42881344058601/100000000000000 : ℝ)^3283
        have hw : |(2622210197/5000000000 : ℝ)|=(2622210197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531354239/2500000000 : ℝ)|^4307 ≤ (655597601221/5000000000000 : ℝ)^3283
        have hw : |(-531354239/2500000000 : ℝ)|=(531354239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s5_3 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325287999/10000000000 : ℝ)*x 0 + (129748743/312500000 : ℝ)*x 1 + (901069357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325287999/10000000000 : ℝ)^4307 ≤ (8325772615739/25000000000000 : ℝ)^3283 := by
    have hnat : (4325287999 : ℕ)^4307*25000000000000^3283 ≤ 8325772615739^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325287999 10000000000 8325772615739 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129748743/312500000 : ℝ)^4307 ≤ (31563309591773/100000000000000 : ℝ)^3283 := by
    have hnat : (129748743 : ℕ)^4307*100000000000000^3283 ≤ 31563309591773^3283*312500000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129748743 312500000 31563309591773 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901069357/2000000000 : ℝ)^4307 ≤ (17566799965493/50000000000000 : ℝ)^3283 := by
    have hnat : (901069357 : ℕ)^4307*50000000000000^3283 ≤ 17566799965493^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901069357 2000000000 17566799965493 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325287999/10000000000 : ℝ), (129748743/312500000 : ℝ), (901069357/2000000000 : ℝ)] ![(8325772615739/25000000000000 : ℝ), (31563309591773/100000000000000 : ℝ), (17566799965493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325287999/10000000000 : ℝ)|^4307 ≤ (8325772615739/25000000000000 : ℝ)^3283
        have hw : |(4325287999/10000000000 : ℝ)|=(4325287999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129748743/312500000 : ℝ)|^4307 ≤ (31563309591773/100000000000000 : ℝ)^3283
        have hw : |(129748743/312500000 : ℝ)|=(129748743/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901069357/2000000000 : ℝ)|^4307 ≤ (17566799965493/50000000000000 : ℝ)^3283
        have hw : |(901069357/2000000000 : ℝ)|=(901069357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s5_4 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2039626097/10000000000 : ℝ)*x 0 + (5245026061/10000000000 : ℝ)*x 1 + (5412210353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2039626097/10000000000 : ℝ)^4307 ≤ (12422030372951/100000000000000 : ℝ)^3283 := by
    have hnat : (2039626097 : ℕ)^4307*100000000000000^3283 ≤ 12422030372951^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039626097 10000000000 12422030372951 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245026061/10000000000 : ℝ)^4307 ≤ (42887841114661/100000000000000 : ℝ)^3283 := by
    have hnat : (5245026061 : ℕ)^4307*100000000000000^3283 ≤ 42887841114661^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245026061 10000000000 42887841114661 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412210353/10000000000 : ℝ)^4307 ≤ (44690128493877/100000000000000 : ℝ)^3283 := by
    have hnat : (5412210353 : ℕ)^4307*100000000000000^3283 ≤ 44690128493877^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412210353 10000000000 44690128493877 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2039626097/10000000000 : ℝ), (5245026061/10000000000 : ℝ), (5412210353/10000000000 : ℝ)] ![(12422030372951/100000000000000 : ℝ), (42887841114661/100000000000000 : ℝ), (44690128493877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2039626097/10000000000 : ℝ)|^4307 ≤ (12422030372951/100000000000000 : ℝ)^3283
        have hw : |(-2039626097/10000000000 : ℝ)|=(2039626097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245026061/10000000000 : ℝ)|^4307 ≤ (42887841114661/100000000000000 : ℝ)^3283
        have hw : |(5245026061/10000000000 : ℝ)|=(5245026061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412210353/10000000000 : ℝ)|^4307 ≤ (44690128493877/100000000000000 : ℝ)^3283
        have hw : |(5412210353/10000000000 : ℝ)|=(5412210353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s5_5 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061121177/2000000000 : ℝ)*x 0 + (-244703367/1250000000 : ℝ)*x 1 + (5412210371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061121177/2000000000 : ℝ)^4307 ≤ (21769433346161/50000000000000 : ℝ)^3283 := by
    have hnat : (1061121177 : ℕ)^4307*50000000000000^3283 ≤ 21769433346161^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061121177 2000000000 21769433346161 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244703367/1250000000 : ℝ)^4307 ≤ (11771004602667/100000000000000 : ℝ)^3283 := by
    have hnat : (244703367 : ℕ)^4307*100000000000000^3283 ≤ 11771004602667^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244703367 1250000000 11771004602667 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412210371/10000000000 : ℝ)^4307 ≤ (11172532172217/25000000000000 : ℝ)^3283 := by
    have hnat : (5412210371 : ℕ)^4307*25000000000000^3283 ≤ 11172532172217^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412210371 10000000000 11172532172217 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061121177/2000000000 : ℝ), (-244703367/1250000000 : ℝ), (5412210371/10000000000 : ℝ)] ![(21769433346161/50000000000000 : ℝ), (11771004602667/100000000000000 : ℝ), (11172532172217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061121177/2000000000 : ℝ)|^4307 ≤ (21769433346161/50000000000000 : ℝ)^3283
        have hw : |(1061121177/2000000000 : ℝ)|=(1061121177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-244703367/1250000000 : ℝ)|^4307 ≤ (11771004602667/100000000000000 : ℝ)^3283
        have hw : |(-244703367/1250000000 : ℝ)|=(244703367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412210371/10000000000 : ℝ)|^4307 ≤ (11172532172217/25000000000000 : ℝ)^3283
        have hw : |(5412210371/10000000000 : ℝ)|=(5412210371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s5_6 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305605863/10000000000 : ℝ)*x 0 + (541221039/1000000000 : ℝ)*x 1 + (-97881347/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305605863/10000000000 : ℝ)^4307 ≤ (21769433227737/50000000000000 : ℝ)^3283 := by
    have hnat : (5305605863 : ℕ)^4307*50000000000000^3283 ≤ 21769433227737^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305605863 10000000000 21769433227737 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541221039/1000000000 : ℝ)^4307 ≤ (44690128894691/100000000000000 : ℝ)^3283 := by
    have hnat : (541221039 : ℕ)^4307*100000000000000^3283 ≤ 44690128894691^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541221039 1000000000 44690128894691 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97881347/500000000 : ℝ)^4307 ≤ (588550231711/5000000000000 : ℝ)^3283 := by
    have hnat : (97881347 : ℕ)^4307*5000000000000^3283 ≤ 588550231711^3283*500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97881347 500000000 588550231711 5000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305605863/10000000000 : ℝ), (541221039/1000000000 : ℝ), (-97881347/500000000 : ℝ)] ![(21769433227737/50000000000000 : ℝ), (44690128894691/100000000000000 : ℝ), (588550231711/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305605863/10000000000 : ℝ)|^4307 ≤ (21769433227737/50000000000000 : ℝ)^3283
        have hw : |(5305605863/10000000000 : ℝ)|=(5305605863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541221039/1000000000 : ℝ)|^4307 ≤ (44690128894691/100000000000000 : ℝ)^3283
        have hw : |(541221039/1000000000 : ℝ)|=(541221039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97881347/500000000 : ℝ)|^4307 ≤ (588550231711/5000000000000 : ℝ)^3283
        have hw : |(-97881347/500000000 : ℝ)|=(97881347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s5_7 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325313627/10000000000 : ℝ)*x 0 + (1126018981/2500000000 : ℝ)*x 1 + (1038309339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325313627/10000000000 : ℝ)^4307 ≤ (16651674668531/50000000000000 : ℝ)^3283 := by
    have hnat : (4325313627 : ℕ)^4307*50000000000000^3283 ≤ 16651674668531^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325313627 10000000000 16651674668531 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126018981/2500000000 : ℝ)^4307 ≤ (35120598912943/100000000000000 : ℝ)^3283 := by
    have hnat : (1126018981 : ℕ)^4307*100000000000000^3283 ≤ 35120598912943^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126018981 2500000000 35120598912943 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038309339/2500000000 : ℝ)^4307 ≤ (3947006466317/12500000000000 : ℝ)^3283 := by
    have hnat : (1038309339 : ℕ)^4307*12500000000000^3283 ≤ 3947006466317^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038309339 2500000000 3947006466317 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325313627/10000000000 : ℝ), (1126018981/2500000000 : ℝ), (1038309339/2500000000 : ℝ)] ![(16651674668531/50000000000000 : ℝ), (35120598912943/100000000000000 : ℝ), (3947006466317/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325313627/10000000000 : ℝ)|^4307 ≤ (16651674668531/50000000000000 : ℝ)^3283
        have hw : |(4325313627/10000000000 : ℝ)|=(4325313627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126018981/2500000000 : ℝ)|^4307 ≤ (35120598912943/100000000000000 : ℝ)^3283
        have hw : |(1126018981/2500000000 : ℝ)|=(1126018981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038309339/2500000000 : ℝ)|^4307 ≤ (3947006466317/12500000000000 : ℝ)^3283
        have hw : |(1038309339/2500000000 : ℝ)|=(1038309339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1347_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11153/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7359/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1389/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1389/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1389/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1389/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1389/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1389/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1389/12500 : ℝ) ^ (2153/512 : ℝ) ≤ (4857936072812601/50000000000000000000 : ℝ) := by
    have hpowers : (1389/12500 : ℝ)^2153 ≤ (4857936072812601/50000000000000000000 : ℝ)^512 := by
      have hnat : (1389 : ℕ)^2153*50000000000000000000^512 ≤ 4857936072812601^512*12500^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1389 12500 4857936072812601 50000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1389/12500 : ℝ)) (X := (4857936072812601/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7381/50000 : ℝ) ^ (2153/512 : ℝ) ≤ (32076772179391357/100000000000000000000 : ℝ) := by
    have hpowers : (7381/50000 : ℝ)^2153 ≤ (32076772179391357/100000000000000000000 : ℝ)^512 := by
      have hnat : (7381 : ℕ)^2153*100000000000000000000^512 ≤ 32076772179391357^512*50000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7381 50000 32076772179391357 100000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7381/50000 : ℝ)) (X := (32076772179391357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004857936072812601/25000000000000000000 : ℝ) ≤ (10000462067645041/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (25004857936072812601/25000000000000000000 : ℝ)^512 ≤ (10000462067645041/10000000000000000 : ℝ)^2153 := by
      have hnat : (25004857936072812601 : ℕ)^512*10000000000000000^2153 ≤ 10000462067645041^2153*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004857936072812601 25000000000000000000 10000462067645041 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000462067645041/10000000000000000 : ℝ)) (X := (25004857936072812601/25000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041792644325016559/100000000000000000000 : ℝ) ≤ (10000993703051299/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (100041792644325016559/100000000000000000000 : ℝ)^512 ≤ (10000993703051299/10000000000000000 : ℝ)^2153 := by
      have hnat : (100041792644325016559 : ℕ)^512*10000000000000000^2153 ≤ 10000993703051299^2153*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041792644325016559 100000000000000000000 10000993703051299 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000993703051299/10000000000000000 : ℝ)) (X := (100041792644325016559/100000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032076772179391357/50000000000000000000 : ℝ) ≤ (10001525338457557/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50032076772179391357/50000000000000000000 : ℝ)^512 ≤ (10001525338457557/10000000000000000 : ℝ)^2153 := by
      have hnat : (50032076772179391357 : ℕ)^512*10000000000000000^2153 ≤ 10001525338457557^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032076772179391357 50000000000000000000 10001525338457557 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001525338457557/10000000000000000 : ℝ)) (X := (50032076772179391357/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4857936072812601/50000000000000000000 : ℝ) ≤ ((18244935740817860929/18250000000000000000 : ℝ)+2*(265817703129/182500000000000 : ℝ)*(1389/12500 : ℝ))^(2153/512 : ℝ) := by
    rw [show (18244935740817860929/18250000000000000000 : ℝ)+2*(265817703129/182500000000000 : ℝ)*(1389/12500 : ℝ)=(10000462067645041/10000000000000000 : ℝ) by norm_num, show 1+2*(4857936072812601/50000000000000000000 : ℝ)=(25004857936072812601/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32076772179391357/100000000000000000000 : ℝ)+(4857936072812601/50000000000000000000 : ℝ) ≤ ((18244935740817860929/18250000000000000000 : ℝ)+(265817703129/182500000000000 : ℝ)*((7381/50000 : ℝ)+(1389/12500 : ℝ)))^(2153/512 : ℝ) := by
    rw [show (18244935740817860929/18250000000000000000 : ℝ)+(265817703129/182500000000000 : ℝ)*((7381/50000 : ℝ)+(1389/12500 : ℝ))=(10000993703051299/10000000000000000 : ℝ) by norm_num, show 1+(32076772179391357/100000000000000000000 : ℝ)+(4857936072812601/50000000000000000000 : ℝ)=(100041792644325016559/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32076772179391357/100000000000000000000 : ℝ) ≤ ((18244935740817860929/18250000000000000000 : ℝ)+2*(265817703129/182500000000000 : ℝ)*(7381/50000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (18244935740817860929/18250000000000000000 : ℝ)+2*(265817703129/182500000000000 : ℝ)*(7381/50000 : ℝ)=(10001525338457557/10000000000000000 : ℝ) by norm_num, show 1+2*(32076772179391357/100000000000000000000 : ℝ)=(50032076772179391357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18244935740817860929/18250000000000000000 : ℝ)*(X 1 0+X 2 0)+(265817703129/182500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (18244935740817860929/18250000000000000000 : ℝ)) (alpha := (265817703129/182500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18244935740817860929/18250000000000000000 : ℝ)*(X 0 1+X 2 1)+(265817703129/182500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (18244935740817860929/18250000000000000000 : ℝ)) (alpha := (265817703129/182500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18244935740817860929/18250000000000000000 : ℝ)*(X 0 2+X 1 2)+(265817703129/182500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (18244935740817860929/18250000000000000000 : ℝ)) (alpha := (265817703129/182500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-254951731/1250000000 : ℝ)*X 0 0+(2706409577/5000000000 : ℝ)*X 0 1+(41955363/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337251633/2500000000 : ℝ)*X 1 0+(-265677123/1250000000 : ℝ)*X 1 1+(104888407/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349006509/10000000000 : ℝ)*X 2 0+(2622210197/5000000000 : ℝ)*X 2 1+(-531354239/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325287999/10000000000 : ℝ)*X 0 0+(129748743/312500000 : ℝ)*X 0 1+(901069357/2000000000 : ℝ)*X 0 2+(4325287999/10000000000 : ℝ)*X 1 0+(129748743/312500000 : ℝ)*X 1 1+(901069357/2000000000 : ℝ)*X 1 2+(4325287999/10000000000 : ℝ)*X 2 0+(129748743/312500000 : ℝ)*X 2 1+(901069357/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2039626097/10000000000 : ℝ)*X 0 0+(5245026061/10000000000 : ℝ)*X 0 1+(5412210353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061121177/2000000000 : ℝ)*X 1 0+(-244703367/1250000000 : ℝ)*X 1 1+(5412210371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305605863/10000000000 : ℝ)*X 2 0+(541221039/1000000000 : ℝ)*X 2 1+(-97881347/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325313627/10000000000 : ℝ)*X 0 0+(1126018981/2500000000 : ℝ)*X 0 1+(1038309339/2500000000 : ℝ)*X 0 2+(4325313627/10000000000 : ℝ)*X 1 0+(1126018981/2500000000 : ℝ)*X 1 1+(1038309339/2500000000 : ℝ)*X 1 2+(4325313627/10000000000 : ℝ)*X 2 0+(1126018981/2500000000 : ℝ)*X 2 1+(1038309339/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1924811886178762572567527271/228125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1670835327/100000000000000 : ℝ)*(base19) + (773608299/50000000000000 : ℝ)*(base23) + (10493107/20000000000000 : ℝ)*(lower2) + (115143327/50000000000000 : ℝ)*(upper3) + (187493633/100000000000000 : ℝ)*(upper5) + (2192035264976933/50000000000000 : ℝ)*(major0) + (2192035264976933/50000000000000 : ℝ)*(major1) + (2192035264976933/50000000000000 : ℝ)*(major2) + (5938318448082199/100000000000000 : ℝ)*(sp0) + (1187669904666691/20000000000000 : ℝ)*(sp1) + (742293705869023/12500000000000 : ℝ)*(sp2) + (1414886833981313/50000000000000 : ℝ)*(sp3) + (32746086583/100000000000000 : ℝ)*(sp4) + (15916525261/100000000000000 : ℝ)*(sp7) + (1414894792243943/50000000000000 : ℝ)*(f.failure) + (2969175597084391/50000000000000 : ℝ)*(f.sum) + (3986659198741/2281250000000000000000000000 : ℝ)*base65 + (13146345615539849243/912500000000000000000000000000000 : ℝ)*base68 + (4455128588952349243/912500000000000000000000000000000 : ℝ)*base70 + (9971719728489849243/912500000000000000000000000000000 : ℝ)*base72 + (9357518080393/4562500000000000000000000000 : ℝ)*base74 + (15752253467677349243/912500000000000000000000000000000 : ℝ)*base76 + (7251226534839849243/912500000000000000000000000000000 : ℝ)*base78 + (6197412210072650757/912500000000000000000000000000000 : ℝ)*base79 + (5864203905241/2281250000000000000000000000 : ℝ)*base81 + (5349413/625000000000000000000 : ℝ)*base90 + (5349413/625000000000000000000 : ℝ)*base92 + (5349413/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4433917517951908382521792527/912500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (897244657/100000000000000 : ℝ)*(base19) + (889740797/100000000000000 : ℝ)*(base23) + (118491899/100000000000000 : ℝ)*(upper3) + (249653/4000000000000 : ℝ)*(lower4) + (95803983/100000000000000 : ℝ)*(upper5) + (4415868086042021/100000000000000 : ℝ)*(major0) + (4415868086042021/100000000000000 : ℝ)*(major1) + (4415868086042021/100000000000000 : ℝ)*(major2) + (4528154189/25000000000000 : ℝ)*(sp1) + (4697307853/25000000000000 : ℝ)*(sp2) + (373838876946011/6250000000000 : ℝ)*(sp4) + (2990701510637381/50000000000000 : ℝ)*(sp5) + (5981402352163967/100000000000000 : ℝ)*(sp6) + (712578494744567/25000000000000 : ℝ)*(sp7) + (712578494744567/25000000000000 : ℝ)*(f.failure) + (373838876946011/6250000000000 : ℝ)*(f.sum) + (22361581387209/9125000000000000000000000000 : ℝ)*base65 + (3903634784001002491/1825000000000000000000000000000000 : ℝ)*base68 + (18195405365601002491/1825000000000000000000000000000000 : ℝ)*base70 + (1992976296248997509/1825000000000000000000000000000000 : ℝ)*base71 + (4991277092291/9125000000000000000000000000 : ℝ)*base74 + (4882976741848997509/1825000000000000000000000000000000 : ℝ)*base75 + (14472127471026002491/1825000000000000000000000000000000 : ℝ)*base78 + (20874949851651002491/1825000000000000000000000000000000 : ℝ)*base80 + (58735532360209/9125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1771997/312500000000000000000 : ℝ)*base90 + (1771997/312500000000000000000 : ℝ)*base92 + (1771997/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1347_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1347_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1347_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4021/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2471/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1347_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1347_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1347_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4021/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2471/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1347_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
