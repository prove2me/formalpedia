-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1466_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:09:23.11908+00:00
-- url     : https://prove2.me/submissions/54c8a8bd-1cb3-4988-9911-3b2c51035768

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
theorem support_rectangle_w1466_s0_0 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-867864973/5000000000 : ℝ)*x 0 + (5949136079/10000000000 : ℝ)*x 1 + (2417576123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867864973/5000000000 : ℝ)^4429 ≤ (10251051609701/100000000000000 : ℝ)^3405 := by
    have hnat : (867864973 : ℕ)^4429*100000000000000^3405 ≤ 10251051609701^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867864973 5000000000 10251051609701 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5949136079/10000000000 : ℝ)^4429 ≤ (25444532684977/50000000000000 : ℝ)^3405 := by
    have hnat : (5949136079 : ℕ)^4429*50000000000000^3405 ≤ 25444532684977^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5949136079 10000000000 25444532684977 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2417576123/5000000000 : ℝ)^4429 ≤ (38859883012079/100000000000000 : ℝ)^3405 := by
    have hnat : (2417576123 : ℕ)^4429*100000000000000^3405 ≤ 38859883012079^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417576123 5000000000 38859883012079 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-867864973/5000000000 : ℝ), (5949136079/10000000000 : ℝ), (2417576123/5000000000 : ℝ)] ![(10251051609701/100000000000000 : ℝ), (25444532684977/50000000000000 : ℝ), (38859883012079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-867864973/5000000000 : ℝ)|^4429 ≤ (10251051609701/100000000000000 : ℝ)^3405
        have hw : |(-867864973/5000000000 : ℝ)|=(867864973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5949136079/10000000000 : ℝ)|^4429 ≤ (25444532684977/50000000000000 : ℝ)^3405
        have hw : |(5949136079/10000000000 : ℝ)|=(5949136079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2417576123/5000000000 : ℝ)|^4429 ≤ (38859883012079/100000000000000 : ℝ)^3405
        have hw : |(2417576123/5000000000 : ℝ)|=(2417576123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s0_1 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2744027347/5000000000 : ℝ)*x 0 + (-2363947993/10000000000 : ℝ)*x 1 + (4835152219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2744027347/5000000000 : ℝ)^4429 ≤ (4581974178727/10000000000000 : ℝ)^3405 := by
    have hnat : (2744027347 : ℕ)^4429*10000000000000^3405 ≤ 4581974178727^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744027347 5000000000 4581974178727 10000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2363947993/10000000000 : ℝ)^4429 ≤ (3064075094221/20000000000000 : ℝ)^3405 := by
    have hnat : (2363947993 : ℕ)^4429*20000000000000^3405 ≤ 3064075094221^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2363947993 10000000000 3064075094221 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4835152219/10000000000 : ℝ)^4429 ≤ (38859882729823/100000000000000 : ℝ)^3405 := by
    have hnat : (4835152219 : ℕ)^4429*100000000000000^3405 ≤ 38859882729823^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4835152219 10000000000 38859882729823 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2744027347/5000000000 : ℝ), (-2363947993/10000000000 : ℝ), (4835152219/10000000000 : ℝ)] ![(4581974178727/10000000000000 : ℝ), (3064075094221/20000000000000 : ℝ), (38859882729823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2744027347/5000000000 : ℝ)|^4429 ≤ (4581974178727/10000000000000 : ℝ)^3405
        have hw : |(2744027347/5000000000 : ℝ)|=(2744027347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2363947993/10000000000 : ℝ)|^4429 ≤ (3064075094221/20000000000000 : ℝ)^3405
        have hw : |(-2363947993/10000000000 : ℝ)|=(2363947993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4835152219/10000000000 : ℝ)|^4429 ≤ (38859882729823/100000000000000 : ℝ)^3405
        have hw : |(4835152219/10000000000 : ℝ)|=(4835152219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s0_2 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2744027377/5000000000 : ℝ)*x 0 + (4835152179/10000000000 : ℝ)*x 1 + (-1181973983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2744027377/5000000000 : ℝ)^4429 ≤ (2290987121943/5000000000000 : ℝ)^3405 := by
    have hnat : (2744027377 : ℕ)^4429*5000000000000^3405 ≤ 2290987121943^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744027377 5000000000 2290987121943 5000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4835152179/10000000000 : ℝ)^4429 ≤ (7771976462333/20000000000000 : ℝ)^3405 := by
    have hnat : (4835152179 : ℕ)^4429*20000000000000^3405 ≤ 7771976462333^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4835152179 10000000000 7771976462333 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1181973983/5000000000 : ℝ)^4429 ≤ (15320375243499/100000000000000 : ℝ)^3405 := by
    have hnat : (1181973983 : ℕ)^4429*100000000000000^3405 ≤ 15320375243499^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181973983 5000000000 15320375243499 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2744027377/5000000000 : ℝ), (4835152179/10000000000 : ℝ), (-1181973983/5000000000 : ℝ)] ![(2290987121943/5000000000000 : ℝ), (7771976462333/20000000000000 : ℝ), (15320375243499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2744027377/5000000000 : ℝ)|^4429 ≤ (2290987121943/5000000000000 : ℝ)^3405
        have hw : |(2744027377/5000000000 : ℝ)|=(2744027377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4835152179/10000000000 : ℝ)|^4429 ≤ (7771976462333/20000000000000 : ℝ)^3405
        have hw : |(4835152179/10000000000 : ℝ)|=(4835152179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1181973983/5000000000 : ℝ)|^4429 ≤ (15320375243499/100000000000000 : ℝ)^3405
        have hw : |(-1181973983/5000000000 : ℝ)|=(1181973983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s0_3 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039447151/2500000000 : ℝ)*x 0 + (123675247/400000000 : ℝ)*x 1 + (5536276031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039447151/2500000000 : ℝ)^4429 ≤ (31933115309793/100000000000000 : ℝ)^3405 := by
    have hnat : (1039447151 : ℕ)^4429*100000000000000^3405 ≤ 31933115309793^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039447151 2500000000 31933115309793 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123675247/400000000 : ℝ)^4429 ≤ (21722777197631/100000000000000 : ℝ)^3405 := by
    have hnat : (123675247 : ℕ)^4429*100000000000000^3405 ≤ 21722777197631^3405*400000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123675247 400000000 21722777197631 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5536276031/10000000000 : ℝ)^4429 ≤ (23172053738243/50000000000000 : ℝ)^3405 := by
    have hnat : (5536276031 : ℕ)^4429*50000000000000^3405 ≤ 23172053738243^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536276031 10000000000 23172053738243 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039447151/2500000000 : ℝ), (123675247/400000000 : ℝ), (5536276031/10000000000 : ℝ)] ![(31933115309793/100000000000000 : ℝ), (21722777197631/100000000000000 : ℝ), (23172053738243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039447151/2500000000 : ℝ)|^4429 ≤ (31933115309793/100000000000000 : ℝ)^3405
        have hw : |(1039447151/2500000000 : ℝ)|=(1039447151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(123675247/400000000 : ℝ)|^4429 ≤ (21722777197631/100000000000000 : ℝ)^3405
        have hw : |(123675247/400000000 : ℝ)|=(123675247/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5536276031/10000000000 : ℝ)|^4429 ≤ (23172053738243/50000000000000 : ℝ)^3405
        have hw : |(5536276031/10000000000 : ℝ)|=(5536276031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s0_4 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-173966347/1000000000 : ℝ)*x 0 + (4863796517/10000000000 : ℝ)*x 1 + (5919460351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173966347/1000000000 : ℝ)^4429 ≤ (5140639634561/50000000000000 : ℝ)^3405 := by
    have hnat : (173966347 : ℕ)^4429*50000000000000^3405 ≤ 5140639634561^3405*1000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173966347 1000000000 5140639634561 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4863796517/10000000000 : ℝ)^4429 ≤ (39159594809677/100000000000000 : ℝ)^3405 := by
    have hnat : (4863796517 : ℕ)^4429*100000000000000^3405 ≤ 39159594809677^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4863796517 10000000000 39159594809677 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5919460351/10000000000 : ℝ)^4429 ≤ (50559125905367/100000000000000 : ℝ)^3405 := by
    have hnat : (5919460351 : ℕ)^4429*100000000000000^3405 ≤ 50559125905367^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5919460351 10000000000 50559125905367 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-173966347/1000000000 : ℝ), (4863796517/10000000000 : ℝ), (5919460351/10000000000 : ℝ)] ![(5140639634561/50000000000000 : ℝ), (39159594809677/100000000000000 : ℝ), (50559125905367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-173966347/1000000000 : ℝ)|^4429 ≤ (5140639634561/50000000000000 : ℝ)^3405
        have hw : |(-173966347/1000000000 : ℝ)|=(173966347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4863796517/10000000000 : ℝ)|^4429 ≤ (39159594809677/100000000000000 : ℝ)^3405
        have hw : |(4863796517/10000000000 : ℝ)|=(4863796517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5919460351/10000000000 : ℝ)|^4429 ≤ (50559125905367/100000000000000 : ℝ)^3405
        have hw : |(5919460351/10000000000 : ℝ)|=(5919460351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s0_5 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5183986549/10000000000 : ℝ)*x 0 + (-639820023/5000000000 : ℝ)*x 1 + (2959730099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183986549/10000000000 : ℝ)^4429 ≤ (21272744905199/50000000000000 : ℝ)^3405 := by
    have hnat : (5183986549 : ℕ)^4429*50000000000000^3405 ≤ 21272744905199^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183986549 10000000000 21272744905199 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639820023/5000000000 : ℝ)^4429 ≤ (3447692982931/50000000000000 : ℝ)^3405 := by
    have hnat : (639820023 : ℕ)^4429*50000000000000^3405 ≤ 3447692982931^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639820023 5000000000 3447692982931 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2959730099/5000000000 : ℝ)^4429 ≤ (50559124205569/100000000000000 : ℝ)^3405 := by
    have hnat : (2959730099 : ℕ)^4429*100000000000000^3405 ≤ 50559124205569^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2959730099 5000000000 50559124205569 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183986549/10000000000 : ℝ), (-639820023/5000000000 : ℝ), (2959730099/5000000000 : ℝ)] ![(21272744905199/50000000000000 : ℝ), (3447692982931/50000000000000 : ℝ), (50559124205569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183986549/10000000000 : ℝ)|^4429 ≤ (21272744905199/50000000000000 : ℝ)^3405
        have hw : |(5183986549/10000000000 : ℝ)|=(5183986549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-639820023/5000000000 : ℝ)|^4429 ≤ (3447692982931/50000000000000 : ℝ)^3405
        have hw : |(-639820023/5000000000 : ℝ)|=(639820023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2959730099/5000000000 : ℝ)|^4429 ≤ (50559124205569/100000000000000 : ℝ)^3405
        have hw : |(2959730099/5000000000 : ℝ)|=(2959730099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s0_6 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2591993263/5000000000 : ℝ)*x 0 + (5919460381/10000000000 : ℝ)*x 1 + (-79977487/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591993263/5000000000 : ℝ)^4429 ≤ (42545489564867/100000000000000 : ℝ)^3405 := by
    have hnat : (2591993263 : ℕ)^4429*100000000000000^3405 ≤ 42545489564867^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591993263 5000000000 42545489564867 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5919460381/10000000000 : ℝ)^4429 ≤ (50559126238661/100000000000000 : ℝ)^3405 := by
    have hnat : (5919460381 : ℕ)^4429*100000000000000^3405 ≤ 50559126238661^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5919460381 10000000000 50559126238661 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79977487/625000000 : ℝ)^4429 ≤ (3447692092781/50000000000000 : ℝ)^3405 := by
    have hnat : (79977487 : ℕ)^4429*50000000000000^3405 ≤ 3447692092781^3405*625000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79977487 625000000 3447692092781 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591993263/5000000000 : ℝ), (5919460381/10000000000 : ℝ), (-79977487/625000000 : ℝ)] ![(42545489564867/100000000000000 : ℝ), (50559126238661/100000000000000 : ℝ), (3447692092781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591993263/5000000000 : ℝ)|^4429 ≤ (42545489564867/100000000000000 : ℝ)^3405
        have hw : |(2591993263/5000000000 : ℝ)|=(2591993263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5919460381/10000000000 : ℝ)|^4429 ≤ (50559126238661/100000000000000 : ℝ)^3405
        have hw : |(5919460381/10000000000 : ℝ)|=(5919460381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79977487/625000000 : ℝ)|^4429 ≤ (3447692092781/50000000000000 : ℝ)^3405
        have hw : |(-79977487/625000000 : ℝ)|=(79977487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s0_7 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4166419327/10000000000 : ℝ)*x 0 + (2736711311/5000000000 : ℝ)*x 1 + (631399633/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166419327/10000000000 : ℝ)^4429 ≤ (32019363521157/100000000000000 : ℝ)^3405 := by
    have hnat : (4166419327 : ℕ)^4429*100000000000000^3405 ≤ 32019363521157^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166419327 10000000000 32019363521157 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736711311/5000000000 : ℝ)^4429 ≤ (45660903810521/100000000000000 : ℝ)^3405 := by
    have hnat : (2736711311 : ℕ)^4429*100000000000000^3405 ≤ 45660903810521^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736711311 5000000000 45660903810521 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (631399633/2000000000 : ℝ)^4429 ≤ (22319732653559/100000000000000 : ℝ)^3405 := by
    have hnat : (631399633 : ℕ)^4429*100000000000000^3405 ≤ 22319732653559^3405*2000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631399633 2000000000 22319732653559 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166419327/10000000000 : ℝ), (2736711311/5000000000 : ℝ), (631399633/2000000000 : ℝ)] ![(32019363521157/100000000000000 : ℝ), (45660903810521/100000000000000 : ℝ), (22319732653559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166419327/10000000000 : ℝ)|^4429 ≤ (32019363521157/100000000000000 : ℝ)^3405
        have hw : |(4166419327/10000000000 : ℝ)|=(4166419327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736711311/5000000000 : ℝ)|^4429 ≤ (45660903810521/100000000000000 : ℝ)^3405
        have hw : |(2736711311/5000000000 : ℝ)|=(2736711311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(631399633/2000000000 : ℝ)|^4429 ≤ (22319732653559/100000000000000 : ℝ)^3405
        have hw : |(631399633/2000000000 : ℝ)|=(631399633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1466_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (443/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26093/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4427/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4427 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4427*1^1024 ≤ 0^1024*1^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4427/1024 : ℝ) ≤ (1903745835945997821/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4427 ≤ (1903745835945997821/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4427*100000000000000000000^1024 ≤ 1903745835945997821^1024*5^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1903745835945997821 100000000000000000000 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1903745835945997821/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4427 := by
      have hnat : (1 : ℕ)^1024*1^4427 ≤ 1^4427*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101903745835945997821/100000000000000000000 : ℝ) ≤ (10043716507460619/10000000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (101903745835945997821/100000000000000000000 : ℝ)^1024 ≤ (10043716507460619/10000000000000000 : ℝ)^4427 := by
      have hnat : (101903745835945997821 : ℕ)^1024*10000000000000000^4427 ≤ 10043716507460619^4427*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101903745835945997821 100000000000000000000 10043716507460619 10000000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10043716507460619/10000000000000000 : ℝ)) (X := (101903745835945997821/100000000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51903745835945997821/50000000000000000000 : ℝ) ≤ (5043716507460619/5000000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (51903745835945997821/50000000000000000000 : ℝ)^1024 ≤ (5043716507460619/5000000000000000 : ℝ)^4427 := by
      have hnat : (51903745835945997821 : ℕ)^1024*5000000000000000^4427 ≤ 5043716507460619^4427*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51903745835945997821 50000000000000000000 5043716507460619 5000000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5043716507460619/5000000000000000 : ℝ)) (X := (51903745835945997821/50000000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(43716507460619/4000000000000000 : ℝ)*(0 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(43716507460619/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1903745835945997821/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(43716507460619/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4427/1024 : ℝ) := by
    rw [show (1 : ℝ)+(43716507460619/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10043716507460619/10000000000000000 : ℝ) by norm_num, show 1+(1903745835945997821/100000000000000000000 : ℝ)+(0 : ℝ)=(101903745835945997821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1903745835945997821/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(43716507460619/4000000000000000 : ℝ)*(2/5 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(43716507460619/4000000000000000 : ℝ)*(2/5 : ℝ)=(5043716507460619/5000000000000000 : ℝ) by norm_num, show 1+2*(1903745835945997821/100000000000000000000 : ℝ)=(51903745835945997821/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(43716507460619/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43716507460619/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(43716507460619/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43716507460619/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(43716507460619/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43716507460619/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-867864973/5000000000 : ℝ)*X 0 0+(5949136079/10000000000 : ℝ)*X 0 1+(2417576123/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2744027347/5000000000 : ℝ)*X 1 0+(-2363947993/10000000000 : ℝ)*X 1 1+(4835152219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2744027377/5000000000 : ℝ)*X 2 0+(4835152179/10000000000 : ℝ)*X 2 1+(-1181973983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1039447151/2500000000 : ℝ)*X 0 0+(123675247/400000000 : ℝ)*X 0 1+(5536276031/10000000000 : ℝ)*X 0 2+(1039447151/2500000000 : ℝ)*X 1 0+(123675247/400000000 : ℝ)*X 1 1+(5536276031/10000000000 : ℝ)*X 1 2+(1039447151/2500000000 : ℝ)*X 2 0+(123675247/400000000 : ℝ)*X 2 1+(5536276031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-173966347/1000000000 : ℝ)*X 0 0+(4863796517/10000000000 : ℝ)*X 0 1+(5919460351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5183986549/10000000000 : ℝ)*X 1 0+(-639820023/5000000000 : ℝ)*X 1 1+(2959730099/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2591993263/5000000000 : ℝ)*X 2 0+(5919460381/10000000000 : ℝ)*X 2 1+(-79977487/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4166419327/10000000000 : ℝ)*X 0 0+(2736711311/5000000000 : ℝ)*X 0 1+(631399633/2000000000 : ℝ)*X 0 2+(4166419327/10000000000 : ℝ)*X 1 0+(2736711311/5000000000 : ℝ)*X 1 1+(631399633/2000000000 : ℝ)*X 1 2+(4166419327/10000000000 : ℝ)*X 2 0+(2736711311/5000000000 : ℝ)*X 2 1+(631399633/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (303857350469370055360617/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35436247/50000000000000 : ℝ)*(base1) + (691936393/50000000000000 : ℝ)*(base19) + (174210881/12500000000000 : ℝ)*(base23) + (10365857/6250000000000 : ℝ)*(upper3) + (176223653/100000000000000 : ℝ)*(upper5) + (163348971211319/25000000000000 : ℝ)*(major0) + (163348971211319/25000000000000 : ℝ)*(major1) + (653395884845277/100000000000000 : ℝ)*(major2) + (89768349251367/10000000000000 : ℝ)*(sp0) + (448843380776663/50000000000000 : ℝ)*(sp1) + (112210843967383/12500000000000 : ℝ)*(sp2) + (409101235626421/100000000000000 : ℝ)*(sp3) + (4723784937/100000000000000 : ℝ)*(sp4) + (2115193953/100000000000000 : ℝ)*(sp7) + (102275855423217/25000000000000 : ℝ)*(f.failure) + (14026377272283/1562500000000 : ℝ)*(f.sum) + (846492381832307/400000000000000000000000000000 : ℝ)*base65 + (3265308534353537/400000000000000000000000000000 : ℝ)*base68 + (34831580753539/100000000000000000000000000000 : ℝ)*base70 + (2756410277953537/400000000000000000000000000000 : ℝ)*base72 + (1314159574632307/400000000000000000000000000000 : ℝ)*base73 + (846468950546461/100000000000000000000000000000 : ℝ)*base75 + (546741497553539/100000000000000000000000000000 : ℝ)*base78 + (137621870153539/100000000000000000000000000000 : ℝ)*base80 + (125954745946461/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (21068653/2500000000000000000000 : ℝ)*base89 + (21068653/2500000000000000000000 : ℝ)*base91 + (3931347/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (161263730327713294964541/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71402871/10000000000000 : ℝ)*(base19) + (145010389/20000000000000 : ℝ)*(base23) + (1474923/25000000000000 : ℝ)*(base32) + (3816251/4000000000000 : ℝ)*(upper3) + (40211793/50000000000000 : ℝ)*(upper5) + (344742780049071/50000000000000 : ℝ)*(major0) + (344742780049071/50000000000000 : ℝ)*(major1) + (344742780049071/50000000000000 : ℝ)*(major2) + (836767491/50000000000000 : ℝ)*(sp1) + (1933119431/100000000000000 : ℝ)*(sp2) + (947271168249373/100000000000000 : ℝ)*(sp4) + (947268780685681/100000000000000 : ℝ)*(sp5) + (947268510077997/100000000000000 : ℝ)*(sp6) + (431699838538061/100000000000000 : ℝ)*(sp7) + (53962480554719/12500000000000 : ℝ)*(f.failure) + (947271168249373/100000000000000 : ℝ)*(f.sum) + (124381643665051/100000000000000000000000000000 : ℝ)*base66 + (626731536565051/200000000000000000000000000000 : ℝ)*base68 + (1135435177565051/200000000000000000000000000000 : ℝ)*base70 + (575624644765051/200000000000000000000000000000 : ℝ)*base72 + (235165928965051/100000000000000000000000000000 : ℝ)*base74 + (748503172165051/200000000000000000000000000000 : ℝ)*base76 + (609061248565051/200000000000000000000000000000 : ℝ)*base78 + (655410169565051/200000000000000000000000000000 : ℝ)*base80 + (245408989465051/100000000000000000000000000000 : ℝ)*base82 + (4169629/1250000000000000000000 : ℝ)*base90 + (4169629/1250000000000000000000 : ℝ)*base92 + (4169629/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1466_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1466_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1466_s1_0 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1902008789/10000000000 : ℝ)*x 0 + (2801539719/5000000000 : ℝ)*x 1 + (5074533599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1902008789/10000000000 : ℝ)^4429 ≤ (11546412339257/100000000000000 : ℝ)^3405 := by
    have hnat : (1902008789 : ℕ)^4429*100000000000000^3405 ≤ 11546412339257^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902008789 10000000000 11546412339257 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2801539719/5000000000 : ℝ)^4429 ≤ (23536403959951/50000000000000 : ℝ)^3405 := by
    have hnat : (2801539719 : ℕ)^4429*50000000000000^3405 ≤ 23536403959951^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2801539719 5000000000 23536403959951 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5074533599/10000000000 : ℝ)^4429 ≤ (2586298732747/6250000000000 : ℝ)^3405 := by
    have hnat : (5074533599 : ℕ)^4429*6250000000000^3405 ≤ 2586298732747^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074533599 10000000000 2586298732747 6250000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1902008789/10000000000 : ℝ), (2801539719/5000000000 : ℝ), (5074533599/10000000000 : ℝ)] ![(11546412339257/100000000000000 : ℝ), (23536403959951/50000000000000 : ℝ), (2586298732747/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1902008789/10000000000 : ℝ)|^4429 ≤ (11546412339257/100000000000000 : ℝ)^3405
        have hw : |(-1902008789/10000000000 : ℝ)|=(1902008789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2801539719/5000000000 : ℝ)|^4429 ≤ (23536403959951/50000000000000 : ℝ)^3405
        have hw : |(2801539719/5000000000 : ℝ)|=(2801539719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5074533599/10000000000 : ℝ)|^4429 ≤ (2586298732747/6250000000000 : ℝ)^3405
        have hw : |(5074533599/10000000000 : ℝ)|=(5074533599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s1_1 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269761601/500000000 : ℝ)*x 0 + (-2182032553/10000000000 : ℝ)*x 1 + (40596279/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269761601/500000000 : ℝ)^4429 ≤ (8962855558319/20000000000000 : ℝ)^3405 := by
    have hnat : (269761601 : ℕ)^4429*20000000000000^3405 ≤ 8962855558319^3405*500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269761601 500000000 8962855558319 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182032553/10000000000 : ℝ)^4429 ≤ (86280805861/625000000000 : ℝ)^3405 := by
    have hnat : (2182032553 : ℕ)^4429*625000000000^3405 ≤ 86280805861^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182032553 10000000000 86280805861 625000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40596279/80000000 : ℝ)^4429 ≤ (41380793258439/100000000000000 : ℝ)^3405 := by
    have hnat : (40596279 : ℕ)^4429*100000000000000^3405 ≤ 41380793258439^3405*80000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40596279 80000000 41380793258439 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269761601/500000000 : ℝ), (-2182032553/10000000000 : ℝ), (40596279/80000000 : ℝ)] ![(8962855558319/20000000000000 : ℝ), (86280805861/625000000000 : ℝ), (41380793258439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269761601/500000000 : ℝ)|^4429 ≤ (8962855558319/20000000000000 : ℝ)^3405
        have hw : |(269761601/500000000 : ℝ)|=(269761601/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182032553/10000000000 : ℝ)|^4429 ≤ (86280805861/625000000000 : ℝ)^3405
        have hw : |(-2182032553/10000000000 : ℝ)|=(2182032553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40596279/80000000 : ℝ)|^4429 ≤ (41380793258439/100000000000000 : ℝ)^3405
        have hw : |(40596279/80000000 : ℝ)|=(40596279/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s1_2 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395233089/10000000000 : ℝ)*x 0 + (5074533713/10000000000 : ℝ)*x 1 + (-1091016323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395233089/10000000000 : ℝ)^4429 ≤ (1400446541917/3125000000000 : ℝ)^3405 := by
    have hnat : (5395233089 : ℕ)^4429*3125000000000^3405 ≤ 1400446541917^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395233089 10000000000 1400446541917 3125000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5074533713/10000000000 : ℝ)^4429 ≤ (20690390466573/50000000000000 : ℝ)^3405 := by
    have hnat : (5074533713 : ℕ)^4429*50000000000000^3405 ≤ 20690390466573^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074533713 10000000000 20690390466573 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091016323/5000000000 : ℝ)^4429 ≤ (6902464851541/50000000000000 : ℝ)^3405 := by
    have hnat : (1091016323 : ℕ)^4429*50000000000000^3405 ≤ 6902464851541^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091016323 5000000000 6902464851541 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395233089/10000000000 : ℝ), (5074533713/10000000000 : ℝ), (-1091016323/5000000000 : ℝ)] ![(1400446541917/3125000000000 : ℝ), (20690390466573/50000000000000 : ℝ), (6902464851541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395233089/10000000000 : ℝ)|^4429 ≤ (1400446541917/3125000000000 : ℝ)^3405
        have hw : |(5395233089/10000000000 : ℝ)|=(5395233089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5074533713/10000000000 : ℝ)|^4429 ≤ (20690390466573/50000000000000 : ℝ)^3405
        have hw : |(5074533713/10000000000 : ℝ)|=(5074533713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091016323/5000000000 : ℝ)|^4429 ≤ (6902464851541/50000000000000 : ℝ)^3405
        have hw : |(-1091016323/5000000000 : ℝ)|=(1091016323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s1_3 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133171609/5000000000 : ℝ)*x 0 + (3721020207/10000000000 : ℝ)*x 1 + (2440398111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133171609/5000000000 : ℝ)^4429 ≤ (1651090633547/5000000000000 : ℝ)^3405 := by
    have hnat : (2133171609 : ℕ)^4429*5000000000000^3405 ≤ 1651090633547^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133171609 5000000000 1651090633547 5000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3721020207/10000000000 : ℝ)^4429 ≤ (27640469195223/100000000000000 : ℝ)^3405 := by
    have hnat : (3721020207 : ℕ)^4429*100000000000000^3405 ≤ 27640469195223^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3721020207 10000000000 27640469195223 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2440398111/5000000000 : ℝ)^4429 ≤ (196688590567/500000000000 : ℝ)^3405 := by
    have hnat : (2440398111 : ℕ)^4429*500000000000^3405 ≤ 196688590567^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2440398111 5000000000 196688590567 500000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133171609/5000000000 : ℝ), (3721020207/10000000000 : ℝ), (2440398111/5000000000 : ℝ)] ![(1651090633547/5000000000000 : ℝ), (27640469195223/100000000000000 : ℝ), (196688590567/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133171609/5000000000 : ℝ)|^4429 ≤ (1651090633547/5000000000000 : ℝ)^3405
        have hw : |(2133171609/5000000000 : ℝ)|=(2133171609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3721020207/10000000000 : ℝ)|^4429 ≤ (27640469195223/100000000000000 : ℝ)^3405
        have hw : |(3721020207/10000000000 : ℝ)|=(3721020207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2440398111/5000000000 : ℝ)|^4429 ≤ (196688590567/500000000000 : ℝ)^3405
        have hw : |(2440398111/5000000000 : ℝ)|=(2440398111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s1_4 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1902412767/10000000000 : ℝ)*x 0 + (5080842633/10000000000 : ℝ)*x 1 + (5596661453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1902412767/10000000000 : ℝ)^4429 ≤ (11549602368699/100000000000000 : ℝ)^3405 := by
    have hnat : (1902412767 : ℕ)^4429*100000000000000^3405 ≤ 11549602368699^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902412767 10000000000 11549602368699 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080842633/10000000000 : ℝ)^4429 ≤ (41447711928309/100000000000000 : ℝ)^3405 := by
    have hnat : (5080842633 : ℕ)^4429*100000000000000^3405 ≤ 41447711928309^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080842633 10000000000 41447711928309 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5596661453/10000000000 : ℝ)^4429 ≤ (2350134284169/5000000000000 : ℝ)^3405 := by
    have hnat : (5596661453 : ℕ)^4429*5000000000000^3405 ≤ 2350134284169^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5596661453 10000000000 2350134284169 5000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1902412767/10000000000 : ℝ), (5080842633/10000000000 : ℝ), (5596661453/10000000000 : ℝ)] ![(11549602368699/100000000000000 : ℝ), (41447711928309/100000000000000 : ℝ), (2350134284169/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1902412767/10000000000 : ℝ)|^4429 ≤ (11549602368699/100000000000000 : ℝ)^3405
        have hw : |(-1902412767/10000000000 : ℝ)|=(1902412767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080842633/10000000000 : ℝ)|^4429 ≤ (41447711928309/100000000000000 : ℝ)^3405
        have hw : |(5080842633/10000000000 : ℝ)|=(5080842633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5596661453/10000000000 : ℝ)|^4429 ≤ (2350134284169/5000000000000 : ℝ)^3405
        have hw : |(5596661453/10000000000 : ℝ)|=(5596661453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s1_5 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628421023/5000000000 : ℝ)*x 0 + (-207488217/1250000000 : ℝ)*x 1 + (2798330733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628421023/5000000000 : ℝ)^4429 ≤ (10831219748391/25000000000000 : ℝ)^3405 := by
    have hnat : (2628421023 : ℕ)^4429*25000000000000^3405 ≤ 10831219748391^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628421023 5000000000 10831219748391 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207488217/1250000000 : ℝ)^4429 ≤ (302263598997/3125000000000 : ℝ)^3405 := by
    have hnat : (207488217 : ℕ)^4429*3125000000000^3405 ≤ 302263598997^3405*1250000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207488217 1250000000 302263598997 3125000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2798330733/5000000000 : ℝ)^4429 ≤ (2937667864087/6250000000000 : ℝ)^3405 := by
    have hnat : (2798330733 : ℕ)^4429*6250000000000^3405 ≤ 2937667864087^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2798330733 5000000000 2937667864087 6250000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628421023/5000000000 : ℝ), (-207488217/1250000000 : ℝ), (2798330733/5000000000 : ℝ)] ![(10831219748391/25000000000000 : ℝ), (302263598997/3125000000000 : ℝ), (2937667864087/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628421023/5000000000 : ℝ)|^4429 ≤ (10831219748391/25000000000000 : ℝ)^3405
        have hw : |(2628421023/5000000000 : ℝ)|=(2628421023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207488217/1250000000 : ℝ)|^4429 ≤ (302263598997/3125000000000 : ℝ)^3405
        have hw : |(-207488217/1250000000 : ℝ)|=(207488217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2798330733/5000000000 : ℝ)|^4429 ≤ (2937667864087/6250000000000 : ℝ)^3405
        have hw : |(2798330733/5000000000 : ℝ)|=(2798330733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s1_6 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314210529/2500000000 : ℝ)*x 0 + (223866457/400000000 : ℝ)*x 1 + (-51872053/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314210529/2500000000 : ℝ)^4429 ≤ (21662439871987/50000000000000 : ℝ)^3405 := by
    have hnat : (1314210529 : ℕ)^4429*50000000000000^3405 ≤ 21662439871987^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314210529 2500000000 21662439871987 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223866457/400000000 : ℝ)^4429 ≤ (47002685377507/100000000000000 : ℝ)^3405 := by
    have hnat : (223866457 : ℕ)^4429*100000000000000^3405 ≤ 47002685377507^3405*400000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223866457 400000000 47002685377507 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51872053/312500000 : ℝ)^4429 ≤ (2418108716181/25000000000000 : ℝ)^3405 := by
    have hnat : (51872053 : ℕ)^4429*25000000000000^3405 ≤ 2418108716181^3405*312500000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51872053 312500000 2418108716181 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314210529/2500000000 : ℝ), (223866457/400000000 : ℝ), (-51872053/312500000 : ℝ)] ![(21662439871987/50000000000000 : ℝ), (47002685377507/100000000000000 : ℝ), (2418108716181/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314210529/2500000000 : ℝ)|^4429 ≤ (21662439871987/50000000000000 : ℝ)^3405
        have hw : |(1314210529/2500000000 : ℝ)|=(1314210529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223866457/400000000 : ℝ)|^4429 ≤ (47002685377507/100000000000000 : ℝ)^3405
        have hw : |(223866457/400000000 : ℝ)|=(223866457/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51872053/312500000 : ℝ)|^4429 ≤ (2418108716181/25000000000000 : ℝ)^3405
        have hw : |(-51872053/312500000 : ℝ)|=(51872053/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s1_7 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133615071/5000000000 : ℝ)*x 0 + (4866953457/10000000000 : ℝ)*x 1 + (933775297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133615071/5000000000 : ℝ)^4429 ≤ (4128842788133/12500000000000 : ℝ)^3405 := by
    have hnat : (2133615071 : ℕ)^4429*12500000000000^3405 ≤ 4128842788133^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133615071 5000000000 4128842788133 12500000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4866953457/10000000000 : ℝ)^4429 ≤ (39192659165201/100000000000000 : ℝ)^3405 := by
    have hnat : (4866953457 : ℕ)^4429*100000000000000^3405 ≤ 39192659165201^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4866953457 10000000000 39192659165201 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933775297/2500000000 : ℝ)^4429 ≤ (13888299260139/50000000000000 : ℝ)^3405 := by
    have hnat : (933775297 : ℕ)^4429*50000000000000^3405 ≤ 13888299260139^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933775297 2500000000 13888299260139 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133615071/5000000000 : ℝ), (4866953457/10000000000 : ℝ), (933775297/2500000000 : ℝ)] ![(4128842788133/12500000000000 : ℝ), (39192659165201/100000000000000 : ℝ), (13888299260139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133615071/5000000000 : ℝ)|^4429 ≤ (4128842788133/12500000000000 : ℝ)^3405
        have hw : |(2133615071/5000000000 : ℝ)|=(2133615071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4866953457/10000000000 : ℝ)|^4429 ≤ (39192659165201/100000000000000 : ℝ)^3405
        have hw : |(4866953457/10000000000 : ℝ)|=(4866953457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(933775297/2500000000 : ℝ)|^4429 ≤ (13888299260139/50000000000000 : ℝ)^3405
        have hw : |(933775297/2500000000 : ℝ)|=(933775297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1466_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1539/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9433/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (443/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (443/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (443/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (443/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (443/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (443/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (443/20000 : ℝ) ^ (4427/1024 : ℝ) ≤ (351252894509/5000000000000000000 : ℝ) := by
    have hpowers : (443/20000 : ℝ)^4427 ≤ (351252894509/5000000000000000000 : ℝ)^1024 := by
      have hnat : (443 : ℕ)^4427*5000000000000000000^1024 ≤ 351252894509^1024*20000^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        443 20000 351252894509 5000000000000000000 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (443/20000 : ℝ)) (X := (351252894509/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26093/100000 : ℝ) ^ (4427/1024 : ℝ) ≤ (75064053312458851/25000000000000000000 : ℝ) := by
    have hpowers : (26093/100000 : ℝ)^4427 ≤ (75064053312458851/25000000000000000000 : ℝ)^1024 := by
      have hnat : (26093 : ℕ)^4427*25000000000000000000^1024 ≤ 75064053312458851^1024*100000^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26093 100000 75064053312458851 25000000000000000000 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26093/100000 : ℝ)) (X := (75064053312458851/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500000351252894509/2500000000000000000 : ℝ) ≤ (10000000324990237/10000000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (2500000351252894509/2500000000000000000 : ℝ)^1024 ≤ (10000000324990237/10000000000000000 : ℝ)^4427 := by
      have hnat : (2500000351252894509 : ℕ)^1024*10000000000000000^4427 ≤ 10000000324990237^4427*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500000351252894509 2500000000000000000 10000000324990237 10000000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000324990237/10000000000000000 : ℝ)) (X := (2500000351252894509/2500000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6268766452394232849/6250000000000000000 : ℝ) ≤ (10006937324320143/10000000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (6268766452394232849/6250000000000000000 : ℝ)^1024 ≤ (10006937324320143/10000000000000000 : ℝ)^4427 := by
      have hnat : (6268766452394232849 : ℕ)^1024*10000000000000000^4427 ≤ 10006937324320143^4427*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6268766452394232849 6250000000000000000 10006937324320143 10000000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006937324320143/10000000000000000 : ℝ)) (X := (6268766452394232849/6250000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12575064053312458851/12500000000000000000 : ℝ) ≤ (10013874323650049/10000000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (12575064053312458851/12500000000000000000 : ℝ)^1024 ≤ (10013874323650049/10000000000000000 : ℝ)^4427 := by
      have hnat : (12575064053312458851 : ℕ)^1024*10000000000000000^4427 ≤ 10013874323650049^4427*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12575064053312458851 12500000000000000000 10013874323650049 10000000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013874323650049/10000000000000000 : ℝ)) (X := (12575064053312458851/12500000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(351252894509/5000000000000000000 : ℝ) ≤ ((119374638426542697753/119390000000000000000 : ℝ)+2*(3468499664953/1193900000000000 : ℝ)*(443/20000 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (119374638426542697753/119390000000000000000 : ℝ)+2*(3468499664953/1193900000000000 : ℝ)*(443/20000 : ℝ)=(10000000324990237/10000000000000000 : ℝ) by norm_num, show 1+2*(351252894509/5000000000000000000 : ℝ)=(2500000351252894509/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(75064053312458851/25000000000000000000 : ℝ)+(351252894509/5000000000000000000 : ℝ) ≤ ((119374638426542697753/119390000000000000000 : ℝ)+(3468499664953/1193900000000000 : ℝ)*((26093/100000 : ℝ)+(443/20000 : ℝ)))^(4427/1024 : ℝ) := by
    rw [show (119374638426542697753/119390000000000000000 : ℝ)+(3468499664953/1193900000000000 : ℝ)*((26093/100000 : ℝ)+(443/20000 : ℝ))=(10006937324320143/10000000000000000 : ℝ) by norm_num, show 1+(75064053312458851/25000000000000000000 : ℝ)+(351252894509/5000000000000000000 : ℝ)=(6268766452394232849/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(75064053312458851/25000000000000000000 : ℝ) ≤ ((119374638426542697753/119390000000000000000 : ℝ)+2*(3468499664953/1193900000000000 : ℝ)*(26093/100000 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (119374638426542697753/119390000000000000000 : ℝ)+2*(3468499664953/1193900000000000 : ℝ)*(26093/100000 : ℝ)=(10013874323650049/10000000000000000 : ℝ) by norm_num, show 1+2*(75064053312458851/25000000000000000000 : ℝ)=(12575064053312458851/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (119374638426542697753/119390000000000000000 : ℝ)*(X 1 0+X 2 0)+(3468499664953/1193900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (443/20000 : ℝ)) (hi := (26093/100000 : ℝ)) (c := (119374638426542697753/119390000000000000000 : ℝ)) (alpha := (3468499664953/1193900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (119374638426542697753/119390000000000000000 : ℝ)*(X 0 1+X 2 1)+(3468499664953/1193900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (443/20000 : ℝ)) (hi := (26093/100000 : ℝ)) (c := (119374638426542697753/119390000000000000000 : ℝ)) (alpha := (3468499664953/1193900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (119374638426542697753/119390000000000000000 : ℝ)*(X 0 2+X 1 2)+(3468499664953/1193900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (443/20000 : ℝ)) (hi := (26093/100000 : ℝ)) (c := (119374638426542697753/119390000000000000000 : ℝ)) (alpha := (3468499664953/1193900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1902008789/10000000000 : ℝ)*X 0 0+(2801539719/5000000000 : ℝ)*X 0 1+(5074533599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((269761601/500000000 : ℝ)*X 1 0+(-2182032553/10000000000 : ℝ)*X 1 1+(40596279/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5395233089/10000000000 : ℝ)*X 2 0+(5074533713/10000000000 : ℝ)*X 2 1+(-1091016323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2133171609/5000000000 : ℝ)*X 0 0+(3721020207/10000000000 : ℝ)*X 0 1+(2440398111/5000000000 : ℝ)*X 0 2+(2133171609/5000000000 : ℝ)*X 1 0+(3721020207/10000000000 : ℝ)*X 1 1+(2440398111/5000000000 : ℝ)*X 1 2+(2133171609/5000000000 : ℝ)*X 2 0+(3721020207/10000000000 : ℝ)*X 2 1+(2440398111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1902412767/10000000000 : ℝ)*X 0 0+(5080842633/10000000000 : ℝ)*X 0 1+(5596661453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628421023/5000000000 : ℝ)*X 1 0+(-207488217/1250000000 : ℝ)*X 1 1+(2798330733/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314210529/2500000000 : ℝ)*X 2 0+(223866457/400000000 : ℝ)*X 2 1+(-51872053/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2133615071/5000000000 : ℝ)*X 0 0+(4866953457/10000000000 : ℝ)*X 0 1+(933775297/2500000000 : ℝ)*X 0 2+(2133615071/5000000000 : ℝ)*X 1 0+(4866953457/10000000000 : ℝ)*X 1 1+(933775297/2500000000 : ℝ)*X 1 2+(2133615071/5000000000 : ℝ)*X 2 0+(4866953457/10000000000 : ℝ)*X 2 1+(933775297/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3178988470703559745382728797/746187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (665296279/100000000000000 : ℝ)*(base19) + (500143547/50000000000000 : ℝ)*(base23) + (52831907/100000000000000 : ℝ)*(upper3) + (2151957/10000000000000 : ℝ)*(upper4) + (61306941/100000000000000 : ℝ)*(upper5) + (344280479913717/25000000000000 : ℝ)*(major0) + (344280479913717/25000000000000 : ℝ)*(major1) + (344280479913717/25000000000000 : ℝ)*(major2) + (1891991939635359/100000000000000 : ℝ)*(sp0) + (1892001162279033/100000000000000 : ℝ)*(sp1) + (946000413644109/50000000000000 : ℝ)*(sp2) + (862238418078291/100000000000000 : ℝ)*(sp3) + (9887939953/100000000000000 : ℝ)*(sp4) + (3451645859/100000000000000 : ℝ)*(sp7) + (17244837394483/2000000000000 : ℝ)*(f.failure) + (118250114223457/6250000000000 : ℝ)*(f.sum) + (207041756663237/29847500000000000000000000000 : ℝ)*base65 + (24585401214067627901/2984750000000000000000000000000000 : ℝ)*base67 + (32364314708500877901/2984750000000000000000000000000000 : ℝ)*base69 + (52371561871788877901/2984750000000000000000000000000000 : ℝ)*base71 + (8274674494259/59695000000000000000000000000 : ℝ)*base73 + (8980791880342872099/2984750000000000000000000000000000 : ℝ)*base76 + (13936313079104377901/2984750000000000000000000000000000 : ℝ)*base77 + (25684896726448377901/2984750000000000000000000000000000 : ℝ)*base79 + (202665514661167/29847500000000000000000000000 : ℝ)*base81 + (2139353/200000000000000000000 : ℝ)*base90 + (2139353/200000000000000000000 : ℝ)*base92 + (2139353/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10905790244822601769939732803/2984750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86388853/12500000000000 : ℝ)*(base19) + (95271237/12500000000000 : ℝ)*(base23) + (6149551/6250000000000 : ℝ)*(upper3) + (8074121/50000000000000 : ℝ)*(lower4) + (152319/195312500000 : ℝ)*(upper5) + (705543166629539/50000000000000 : ℝ)*(major0) + (705543166629539/50000000000000 : ℝ)*(major1) + (705543166629539/50000000000000 : ℝ)*(major2) + (3992268247/100000000000000 : ℝ)*(sp1) + (567998849/12500000000000 : ℝ)*(sp2) + (969332459222127/50000000000000 : ℝ)*(sp4) + (1938660235065183/100000000000000 : ℝ)*(sp5) + (969329806141783/50000000000000 : ℝ)*(sp6) + (27609613321229/3125000000000 : ℝ)*(sp7) + (27609613321229/3125000000000 : ℝ)*(f.failure) + (969332459222127/50000000000000 : ℝ)*(f.sum) + (27934065727381/14923750000000000000000000000 : ℝ)*base65 + (25836710524755574133/5969500000000000000000000000000000 : ℝ)*base68 + (57778699428791574133/5969500000000000000000000000000000 : ℝ)*base70 + (11010503682947574133/5969500000000000000000000000000000 : ℝ)*base72 + (26152206471519/59695000000000000000000000000 : ℝ)*base73 + (36048593228891074133/5969500000000000000000000000000000 : ℝ)*base76 + (20588141320974574133/5969500000000000000000000000000000 : ℝ)*base78 + (36594534299103574133/5969500000000000000000000000000000 : ℝ)*base80 + (147958665283693/29847500000000000000000000000 : ℝ)*base82 + (1769961/312500000000000000000 : ℝ)*base89 + (1769961/312500000000000000000 : ℝ)*base91 + (1769961/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1466_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1539/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9433/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1466_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1466_s2_0 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-483082907/2500000000 : ℝ)*x 0 + (1094848981/2000000000 : ℝ)*x 1 + (5183823679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (483082907/2500000000 : ℝ)^4429 ≤ (11786422149049/100000000000000 : ℝ)^3405 := by
    have hnat : (483082907 : ℕ)^4429*100000000000000^3405 ≤ 11786422149049^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483082907 2500000000 11786422149049 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094848981/2000000000 : ℝ)^4429 ≤ (45669826693693/100000000000000 : ℝ)^3405 := by
    have hnat : (1094848981 : ℕ)^4429*100000000000000^3405 ≤ 45669826693693^3405*2000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094848981 2000000000 45669826693693 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183823679/10000000000 : ℝ)^4429 ≤ (21271875569979/50000000000000 : ℝ)^3405 := by
    have hnat : (5183823679 : ℕ)^4429*50000000000000^3405 ≤ 21271875569979^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183823679 10000000000 21271875569979 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-483082907/2500000000 : ℝ), (1094848981/2000000000 : ℝ), (5183823679/10000000000 : ℝ)] ![(11786422149049/100000000000000 : ℝ), (45669826693693/100000000000000 : ℝ), (21271875569979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-483082907/2500000000 : ℝ)|^4429 ≤ (11786422149049/100000000000000 : ℝ)^3405
        have hw : |(-483082907/2500000000 : ℝ)|=(483082907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094848981/2000000000 : ℝ)|^4429 ≤ (45669826693693/100000000000000 : ℝ)^3405
        have hw : |(1094848981/2000000000 : ℝ)|=(1094848981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183823679/10000000000 : ℝ)|^4429 ≤ (21271875569979/50000000000000 : ℝ)^3405
        have hw : |(5183823679/10000000000 : ℝ)|=(5183823679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s2_1 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072600201/2000000000 : ℝ)*x 0 + (-83291859/400000000 : ℝ)*x 1 + (1036765001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072600201/2000000000 : ℝ)^4429 ≤ (22233179462781/50000000000000 : ℝ)^3405 := by
    have hnat : (1072600201 : ℕ)^4429*50000000000000^3405 ≤ 22233179462781^3405*2000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072600201 2000000000 22233179462781 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83291859/400000000 : ℝ)^4429 ≤ (12989875757441/100000000000000 : ℝ)^3405 := by
    have hnat : (83291859 : ℕ)^4429*100000000000000^3405 ≤ 12989875757441^3405*400000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83291859 400000000 12989875757441 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036765001/2000000000 : ℝ)^4429 ≤ (10635941323803/25000000000000 : ℝ)^3405 := by
    have hnat : (1036765001 : ℕ)^4429*25000000000000^3405 ≤ 10635941323803^3405*2000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036765001 2000000000 10635941323803 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072600201/2000000000 : ℝ), (-83291859/400000000 : ℝ), (1036765001/2000000000 : ℝ)] ![(22233179462781/50000000000000 : ℝ), (12989875757441/100000000000000 : ℝ), (10635941323803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072600201/2000000000 : ℝ)|^4429 ≤ (22233179462781/50000000000000 : ℝ)^3405
        have hw : |(1072600201/2000000000 : ℝ)|=(1072600201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83291859/400000000 : ℝ)|^4429 ≤ (12989875757441/100000000000000 : ℝ)^3405
        have hw : |(-83291859/400000000 : ℝ)|=(83291859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036765001/2000000000 : ℝ)|^4429 ≤ (10635941323803/25000000000000 : ℝ)^3405
        have hw : |(1036765001/2000000000 : ℝ)|=(1036765001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s2_2 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681500953/5000000000 : ℝ)*x 0 + (1295956059/2500000000 : ℝ)*x 1 + (-208229629/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681500953/5000000000 : ℝ)^4429 ≤ (4446636864267/10000000000000 : ℝ)^3405 := by
    have hnat : (2681500953 : ℕ)^4429*10000000000000^3405 ≤ 4446636864267^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681500953 5000000000 4446636864267 10000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295956059/2500000000 : ℝ)^4429 ≤ (21271878543009/50000000000000 : ℝ)^3405 := by
    have hnat : (1295956059 : ℕ)^4429*50000000000000^3405 ≤ 21271878543009^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295956059 2500000000 21271878543009 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208229629/1000000000 : ℝ)^4429 ≤ (1623734282037/12500000000000 : ℝ)^3405 := by
    have hnat : (208229629 : ℕ)^4429*12500000000000^3405 ≤ 1623734282037^3405*1000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208229629 1000000000 1623734282037 12500000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681500953/5000000000 : ℝ), (1295956059/2500000000 : ℝ), (-208229629/1000000000 : ℝ)] ![(4446636864267/10000000000000 : ℝ), (21271878543009/50000000000000 : ℝ), (1623734282037/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681500953/5000000000 : ℝ)|^4429 ≤ (4446636864267/10000000000000 : ℝ)^3405
        have hw : |(2681500953/5000000000 : ℝ)|=(2681500953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295956059/2500000000 : ℝ)|^4429 ≤ (21271878543009/50000000000000 : ℝ)^3405
        have hw : |(1295956059/2500000000 : ℝ)|=(1295956059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208229629/1000000000 : ℝ)|^4429 ≤ (1623734282037/12500000000000 : ℝ)^3405
        have hw : |(-208229629/1000000000 : ℝ)|=(208229629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s2_3 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143962481/5000000000 : ℝ)*x 0 + (3979727457/10000000000 : ℝ)*x 1 + (4616992557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143962481/5000000000 : ℝ)^4429 ≤ (8309814495953/25000000000000 : ℝ)^3405 := by
    have hnat : (2143962481 : ℕ)^4429*25000000000000^3405 ≤ 8309814495953^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143962481 5000000000 8309814495953 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979727457/10000000000 : ℝ)^4429 ≤ (30165847927633/100000000000000 : ℝ)^3405 := by
    have hnat : (3979727457 : ℕ)^4429*100000000000000^3405 ≤ 30165847927633^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979727457 10000000000 30165847927633 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4616992557/10000000000 : ℝ)^4429 ≤ (18297447038249/50000000000000 : ℝ)^3405 := by
    have hnat : (4616992557 : ℕ)^4429*50000000000000^3405 ≤ 18297447038249^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616992557 10000000000 18297447038249 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143962481/5000000000 : ℝ), (3979727457/10000000000 : ℝ), (4616992557/10000000000 : ℝ)] ![(8309814495953/25000000000000 : ℝ), (30165847927633/100000000000000 : ℝ), (18297447038249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143962481/5000000000 : ℝ)|^4429 ≤ (8309814495953/25000000000000 : ℝ)^3405
        have hw : |(2143962481/5000000000 : ℝ)|=(2143962481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979727457/10000000000 : ℝ)|^4429 ≤ (30165847927633/100000000000000 : ℝ)^3405
        have hw : |(3979727457/10000000000 : ℝ)|=(3979727457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4616992557/10000000000 : ℝ)|^4429 ≤ (18297447038249/50000000000000 : ℝ)^3405
        have hw : |(4616992557/10000000000 : ℝ)|=(4616992557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s2_4 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1932398509/10000000000 : ℝ)*x 0 + (5185738539/10000000000 : ℝ)*x 1 + (2736156037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1932398509/10000000000 : ℝ)^4429 ≤ (11786952781629/100000000000000 : ℝ)^3405 := by
    have hnat : (1932398509 : ℕ)^4429*100000000000000^3405 ≤ 11786952781629^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932398509 10000000000 11786952781629 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185738539/10000000000 : ℝ)^4429 ≤ (4256419369941/10000000000000 : ℝ)^3405 := by
    have hnat : (5185738539 : ℕ)^4429*10000000000000^3405 ≤ 4256419369941^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185738539 10000000000 4256419369941 10000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736156037/5000000000 : ℝ)^4429 ≤ (45648853501939/100000000000000 : ℝ)^3405 := by
    have hnat : (2736156037 : ℕ)^4429*100000000000000^3405 ≤ 45648853501939^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736156037 5000000000 45648853501939 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1932398509/10000000000 : ℝ), (5185738539/10000000000 : ℝ), (2736156037/5000000000 : ℝ)] ![(11786952781629/100000000000000 : ℝ), (4256419369941/10000000000000 : ℝ), (45648853501939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1932398509/10000000000 : ℝ)|^4429 ≤ (11786952781629/100000000000000 : ℝ)^3405
        have hw : |(-1932398509/10000000000 : ℝ)|=(1932398509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185738539/10000000000 : ℝ)|^4429 ≤ (4256419369941/10000000000000 : ℝ)^3405
        have hw : |(5185738539/10000000000 : ℝ)|=(5185738539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736156037/5000000000 : ℝ)|^4429 ≤ (45648853501939/100000000000000 : ℝ)^3405
        have hw : |(2736156037/5000000000 : ℝ)|=(2736156037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s2_5 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643651423/5000000000 : ℝ)*x 0 + (-71752343/400000000 : ℝ)*x 1 + (684039/1250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643651423/5000000000 : ℝ)^4429 ≤ (43651707574069/100000000000000 : ℝ)^3405 := by
    have hnat : (2643651423 : ℕ)^4429*100000000000000^3405 ≤ 43651707574069^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643651423 5000000000 43651707574069 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71752343/400000000 : ℝ)^4429 ≤ (5349719858261/50000000000000 : ℝ)^3405 := by
    have hnat : (71752343 : ℕ)^4429*50000000000000^3405 ≤ 5349719858261^3405*400000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71752343 400000000 5349719858261 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684039/1250000 : ℝ)^4429 ≤ (22824426349503/50000000000000 : ℝ)^3405 := by
    have hnat : (684039 : ℕ)^4429*50000000000000^3405 ≤ 22824426349503^3405*1250000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684039 1250000 22824426349503 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643651423/5000000000 : ℝ), (-71752343/400000000 : ℝ), (684039/1250000 : ℝ)] ![(43651707574069/100000000000000 : ℝ), (5349719858261/50000000000000 : ℝ), (22824426349503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643651423/5000000000 : ℝ)|^4429 ≤ (43651707574069/100000000000000 : ℝ)^3405
        have hw : |(2643651423/5000000000 : ℝ)|=(2643651423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-71752343/400000000 : ℝ)|^4429 ≤ (5349719858261/50000000000000 : ℝ)^3405
        have hw : |(-71752343/400000000 : ℝ)|=(71752343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684039/1250000 : ℝ)|^4429 ≤ (22824426349503/50000000000000 : ℝ)^3405
        have hw : |(684039/1250000 : ℝ)|=(684039/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s2_6 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321825649/2500000000 : ℝ)*x 0 + (218892481/400000000 : ℝ)*x 1 + (-896904443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321825649/2500000000 : ℝ)^4429 ≤ (43651704889369/100000000000000 : ℝ)^3405 := by
    have hnat : (1321825649 : ℕ)^4429*100000000000000^3405 ≤ 43651704889369^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321825649 2500000000 43651704889369 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218892481/400000000 : ℝ)^4429 ≤ (45648852970267/100000000000000 : ℝ)^3405 := by
    have hnat : (218892481 : ℕ)^4429*100000000000000^3405 ≤ 45648852970267^3405*400000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218892481 400000000 45648852970267 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896904443/5000000000 : ℝ)^4429 ≤ (668715133087/6250000000000 : ℝ)^3405 := by
    have hnat : (896904443 : ℕ)^4429*6250000000000^3405 ≤ 668715133087^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896904443 5000000000 668715133087 6250000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321825649/2500000000 : ℝ), (218892481/400000000 : ℝ), (-896904443/5000000000 : ℝ)] ![(43651704889369/100000000000000 : ℝ), (45648852970267/100000000000000 : ℝ), (668715133087/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321825649/2500000000 : ℝ)|^4429 ≤ (43651704889369/100000000000000 : ℝ)^3405
        have hw : |(1321825649/2500000000 : ℝ)|=(1321825649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218892481/400000000 : ℝ)|^4429 ≤ (45648852970267/100000000000000 : ℝ)^3405
        have hw : |(218892481/400000000 : ℝ)|=(218892481/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-896904443/5000000000 : ℝ)|^4429 ≤ (668715133087/6250000000000 : ℝ)^3405
        have hw : |(-896904443/5000000000 : ℝ)|=(896904443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s2_7 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2144036417/5000000000 : ℝ)*x 0 + (576598913/1250000000 : ℝ)*x 1 + (1991984059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144036417/5000000000 : ℝ)^4429 ≤ (16620374497507/50000000000000 : ℝ)^3405 := by
    have hnat : (2144036417 : ℕ)^4429*50000000000000^3405 ≤ 16620374497507^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144036417 5000000000 16620374497507 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576598913/1250000000 : ℝ)^4429 ≤ (7310317192333/20000000000000 : ℝ)^3405 := by
    have hnat : (576598913 : ℕ)^4429*20000000000000^3405 ≤ 7310317192333^3405*1250000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576598913 1250000000 7310317192333 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991984059/5000000000 : ℝ)^4429 ≤ (30207665025443/100000000000000 : ℝ)^3405 := by
    have hnat : (1991984059 : ℕ)^4429*100000000000000^3405 ≤ 30207665025443^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991984059 5000000000 30207665025443 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144036417/5000000000 : ℝ), (576598913/1250000000 : ℝ), (1991984059/5000000000 : ℝ)] ![(16620374497507/50000000000000 : ℝ), (7310317192333/20000000000000 : ℝ), (30207665025443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144036417/5000000000 : ℝ)|^4429 ≤ (16620374497507/50000000000000 : ℝ)^3405
        have hw : |(2144036417/5000000000 : ℝ)|=(2144036417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(576598913/1250000000 : ℝ)|^4429 ≤ (7310317192333/20000000000000 : ℝ)^3405
        have hw : |(576598913/1250000000 : ℝ)|=(576598913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1991984059/5000000000 : ℝ)|^4429 ≤ (30207665025443/100000000000000 : ℝ)^3405
        have hw : |(1991984059/5000000000 : ℝ)|=(1991984059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1466_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9433/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1539/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5029/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16199/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9433/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1539/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9433/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1539/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9433/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1539/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9433/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1539/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9433/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1539/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9433/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1539/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1539/20000 : ℝ) ^ (4427/1024 : ℝ) ≤ (1530418249939657/100000000000000000000 : ℝ) := by
    have hpowers : (1539/20000 : ℝ)^4427 ≤ (1530418249939657/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1539 : ℕ)^4427*100000000000000000000^1024 ≤ 1530418249939657^1024*20000^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1539 20000 1530418249939657 100000000000000000000 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1539/20000 : ℝ)) (X := (1530418249939657/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9433/50000 : ℝ) ^ (4427/1024 : ℝ) ≤ (461815496229521/625000000000000000 : ℝ) := by
    have hpowers : (9433/50000 : ℝ)^4427 ≤ (461815496229521/625000000000000000 : ℝ)^1024 := by
      have hnat : (9433 : ℕ)^4427*625000000000000000^1024 ≤ 461815496229521^1024*50000^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9433 50000 461815496229521 625000000000000000 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9433/50000 : ℝ)) (X := (461815496229521/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001530418249939657/50000000000000000000 : ℝ) ≤ (200001415974567/200000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (50001530418249939657/50000000000000000000 : ℝ)^1024 ≤ (200001415974567/200000000000000 : ℝ)^4427 := by
      have hnat : (50001530418249939657 : ℕ)^1024*200000000000000^4427 ≤ 200001415974567^4427*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001530418249939657 50000000000000000000 200001415974567 200000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200001415974567/200000000000000 : ℝ)) (X := (50001530418249939657/50000000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100075420897646663017/100000000000000000000 : ℝ) ≤ (2000348807868219/2000000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (100075420897646663017/100000000000000000000 : ℝ)^1024 ≤ (2000348807868219/2000000000000000 : ℝ)^4427 := by
      have hnat : (100075420897646663017 : ℕ)^1024*2000000000000000^4427 ≤ 2000348807868219^4427*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100075420897646663017 100000000000000000000 2000348807868219 2000000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000348807868219/2000000000000000 : ℝ)) (X := (100075420897646663017/100000000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (312961815496229521/312500000000000000 : ℝ) ≤ (125042715999423/125000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (312961815496229521/312500000000000000 : ℝ)^1024 ≤ (125042715999423/125000000000000 : ℝ)^4427 := by
      have hnat : (312961815496229521 : ℕ)^1024*125000000000000^4427 ≤ 125042715999423^4427*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312961815496229521 312500000000000000 125042715999423 125000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125042715999423/125000000000000 : ℝ)) (X := (312961815496229521/312500000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1530418249939657/100000000000000000000 : ℝ) ≤ ((1116850397195642523/1117100000000000000 : ℝ)+2*(334648122549/223420000000000 : ℝ)*(1539/20000 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (1116850397195642523/1117100000000000000 : ℝ)+2*(334648122549/223420000000000 : ℝ)*(1539/20000 : ℝ)=(200001415974567/200000000000000 : ℝ) by norm_num, show 1+2*(1530418249939657/100000000000000000000 : ℝ)=(50001530418249939657/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(461815496229521/625000000000000000 : ℝ)+(1530418249939657/100000000000000000000 : ℝ) ≤ ((1116850397195642523/1117100000000000000 : ℝ)+(334648122549/223420000000000 : ℝ)*((9433/50000 : ℝ)+(1539/20000 : ℝ)))^(4427/1024 : ℝ) := by
    rw [show (1116850397195642523/1117100000000000000 : ℝ)+(334648122549/223420000000000 : ℝ)*((9433/50000 : ℝ)+(1539/20000 : ℝ))=(2000348807868219/2000000000000000 : ℝ) by norm_num, show 1+(461815496229521/625000000000000000 : ℝ)+(1530418249939657/100000000000000000000 : ℝ)=(100075420897646663017/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(461815496229521/625000000000000000 : ℝ) ≤ ((1116850397195642523/1117100000000000000 : ℝ)+2*(334648122549/223420000000000 : ℝ)*(9433/50000 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (1116850397195642523/1117100000000000000 : ℝ)+2*(334648122549/223420000000000 : ℝ)*(9433/50000 : ℝ)=(125042715999423/125000000000000 : ℝ) by norm_num, show 1+2*(461815496229521/625000000000000000 : ℝ)=(312961815496229521/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1116850397195642523/1117100000000000000 : ℝ)*(X 1 0+X 2 0)+(334648122549/223420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (1539/20000 : ℝ)) (hi := (9433/50000 : ℝ)) (c := (1116850397195642523/1117100000000000000 : ℝ)) (alpha := (334648122549/223420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1116850397195642523/1117100000000000000 : ℝ)*(X 0 1+X 2 1)+(334648122549/223420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (1539/20000 : ℝ)) (hi := (9433/50000 : ℝ)) (c := (1116850397195642523/1117100000000000000 : ℝ)) (alpha := (334648122549/223420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1116850397195642523/1117100000000000000 : ℝ)*(X 0 2+X 1 2)+(334648122549/223420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (1539/20000 : ℝ)) (hi := (9433/50000 : ℝ)) (c := (1116850397195642523/1117100000000000000 : ℝ)) (alpha := (334648122549/223420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-483082907/2500000000 : ℝ)*X 0 0+(1094848981/2000000000 : ℝ)*X 0 1+(5183823679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1072600201/2000000000 : ℝ)*X 1 0+(-83291859/400000000 : ℝ)*X 1 1+(1036765001/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681500953/5000000000 : ℝ)*X 2 0+(1295956059/2500000000 : ℝ)*X 2 1+(-208229629/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2143962481/5000000000 : ℝ)*X 0 0+(3979727457/10000000000 : ℝ)*X 0 1+(4616992557/10000000000 : ℝ)*X 0 2+(2143962481/5000000000 : ℝ)*X 1 0+(3979727457/10000000000 : ℝ)*X 1 1+(4616992557/10000000000 : ℝ)*X 1 2+(2143962481/5000000000 : ℝ)*X 2 0+(3979727457/10000000000 : ℝ)*X 2 1+(4616992557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1932398509/10000000000 : ℝ)*X 0 0+(5185738539/10000000000 : ℝ)*X 0 1+(2736156037/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643651423/5000000000 : ℝ)*X 1 0+(-71752343/400000000 : ℝ)*X 1 1+(684039/1250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321825649/2500000000 : ℝ)*X 2 0+(218892481/400000000 : ℝ)*X 2 1+(-896904443/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2144036417/5000000000 : ℝ)*X 0 0+(576598913/1250000000 : ℝ)*X 0 1+(1991984059/5000000000 : ℝ)*X 0 2+(2144036417/5000000000 : ℝ)*X 1 0+(576598913/1250000000 : ℝ)*X 1 1+(1991984059/5000000000 : ℝ)*X 1 2+(2144036417/5000000000 : ℝ)*X 2 0+(576598913/1250000000 : ℝ)*X 2 1+(1991984059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35313490086195637529067807/6981875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (759396329/100000000000000 : ℝ)*(base19) + (1037851379/100000000000000 : ℝ)*(base23) + (26901511/25000000000000 : ℝ)*(upper3) + (32181483/20000000000000 : ℝ)*(upper4) + (33482749/25000000000000 : ℝ)*(upper5) + (313283854059153/12500000000000 : ℝ)*(major0) + (313283854059153/12500000000000 : ℝ)*(major1) + (313283854059153/12500000000000 : ℝ)*(major2) + (3443293534107/100000000000 : ℝ)*(sp0) + (430414693655449/12500000000000 : ℝ)*(sp1) + (1721658635394271/50000000000000 : ℝ)*(sp2) + (1569213610788473/100000000000000 : ℝ)*(sp3) + (24774532921/100000000000000 : ℝ)*(sp4) + (2394230507/25000000000000 : ℝ)*(sp7) + (1569223187710501/100000000000000 : ℝ)*(f.failure) + (43041478857999/1250000000000 : ℝ)*(f.sum) + (50580657620743/11171000000000000000000000000 : ℝ)*base66 + (83221782810733019/13963750000000000000000000000000 : ℝ)*base67 + (63503364395211769/13963750000000000000000000000000 : ℝ)*base69 + (71598994730599481/13963750000000000000000000000000 : ℝ)*base72 + (63473354605093/11171000000000000000000000000 : ℝ)*base73 + (62549875729570731/13963750000000000000000000000000 : ℝ)*base76 + (43436220791514481/13963750000000000000000000000000 : ℝ)*base78 + (3659643255895731/13963750000000000000000000000000 : ℝ)*base80 + (66137860273941/11171000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (17158609/10000000000000000000000 : ℝ)*base89 + (17158609/10000000000000000000000 : ℝ)*base91 + (17158609/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102751943659804332899280201/13963750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (797630897/50000000000000 : ℝ)*(base19) + (1434749693/100000000000000 : ℝ)*(base23) + (77223371/50000000000000 : ℝ)*(upper3) + (5770001/20000000000000 : ℝ)*(lower4) + (6096897/4000000000000 : ℝ)*(upper5) + (1269944061102829/50000000000000 : ℝ)*(major0) + (1269944061102829/50000000000000 : ℝ)*(major1) + (1269944061102829/50000000000000 : ℝ)*(major2) + (4697054831/25000000000000 : ℝ)*(sp1) + (3057975613/20000000000000 : ℝ)*(sp2) + (436188049453933/12500000000000 : ℝ)*(sp4) + (1744742006075173/50000000000000 : ℝ)*(sp5) + (1744743835501853/50000000000000 : ℝ)*(sp6) + (795135801748629/50000000000000 : ℝ)*(sp7) + (795135801748629/50000000000000 : ℝ)*(f.failure) + (436188049453933/12500000000000 : ℝ)*(f.sum) + (12556443657537/5585500000000000000000000000 : ℝ)*base66 + (122453108832837433/55855000000000000000000000000000 : ℝ)*base68 + (9490909663297433/55855000000000000000000000000000 : ℝ)*base70 + (169514240660737433/55855000000000000000000000000000 : ℝ)*base72 + (129302299291/139637500000000000000000000 : ℝ)*base74 + (126443028986117433/55855000000000000000000000000000 : ℝ)*base76 + (393152484577887433/55855000000000000000000000000000 : ℝ)*base78 + (51291861852792567/55855000000000000000000000000000 : ℝ)*base79 + (725205975113/1396375000000000000000000000 : ℝ)*base81 + (22706561/5000000000000000000000 : ℝ)*base89 + (22706561/5000000000000000000000 : ℝ)*base91 + (22706561/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1466_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9433/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1539/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5029/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16199/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1466_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1466_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5029/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16199/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1466_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1466_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1466_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5029/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16199/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1466_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
