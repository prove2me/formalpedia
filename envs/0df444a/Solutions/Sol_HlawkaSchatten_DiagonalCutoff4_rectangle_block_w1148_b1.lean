-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1148_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:34:30.292145+00:00
-- url     : https://prove2.me/submissions/1ac73b0f-84f7-4044-b96c-645b827d5d8e

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
theorem support_rectangle_w1148_s3_0 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160282513/10000000000 : ℝ)*x 0 + (5428569283/10000000000 : ℝ)*x 1 + (20930557/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160282513/10000000000 : ℝ)^8341 ≤ (6559987698109/50000000000000 : ℝ)^6293 := by
    have hnat : (2160282513 : ℕ)^8341*50000000000000^6293 ≤ 6559987698109^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160282513 10000000000 6559987698109 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428569283/10000000000 : ℝ)^8341 ≤ (22249033228399/50000000000000 : ℝ)^6293 := by
    have hnat : (5428569283 : ℕ)^8341*50000000000000^6293 ≤ 22249033228399^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428569283 10000000000 22249033228399 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20930557/40000000 : ℝ)^8341 ≤ (21190979066917/50000000000000 : ℝ)^6293 := by
    have hnat : (20930557 : ℕ)^8341*50000000000000^6293 ≤ 21190979066917^6293*40000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20930557 40000000 21190979066917 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160282513/10000000000 : ℝ), (5428569283/10000000000 : ℝ), (20930557/40000000 : ℝ)] ![(6559987698109/50000000000000 : ℝ), (22249033228399/50000000000000 : ℝ), (21190979066917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160282513/10000000000 : ℝ)|^8341 ≤ (6559987698109/50000000000000 : ℝ)^6293
        have hw : |(-2160282513/10000000000 : ℝ)|=(2160282513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428569283/10000000000 : ℝ)|^8341 ≤ (22249033228399/50000000000000 : ℝ)^6293
        have hw : |(5428569283/10000000000 : ℝ)|=(5428569283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20930557/40000000 : ℝ)|^8341 ≤ (21190979066917/50000000000000 : ℝ)^6293
        have hw : |(20930557/40000000 : ℝ)|=(20930557/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s3_1 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353651977/10000000000 : ℝ)*x 0 + (-452084463/2000000000 : ℝ)*x 1 + (209305563/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353651977/10000000000 : ℝ)^8341 ≤ (2730371808203/6250000000000 : ℝ)^6293 := by
    have hnat : (5353651977 : ℕ)^8341*6250000000000^6293 ≤ 2730371808203^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353651977 10000000000 2730371808203 6250000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452084463/2000000000 : ℝ)^8341 ≤ (3483023700189/25000000000000 : ℝ)^6293 := by
    have hnat : (452084463 : ℕ)^8341*25000000000000^6293 ≤ 3483023700189^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452084463 2000000000 3483023700189 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209305563/400000000 : ℝ)^8341 ≤ (5297744531891/12500000000000 : ℝ)^6293 := by
    have hnat : (209305563 : ℕ)^8341*12500000000000^6293 ≤ 5297744531891^6293*400000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209305563 400000000 5297744531891 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353651977/10000000000 : ℝ), (-452084463/2000000000 : ℝ), (209305563/400000000 : ℝ)] ![(2730371808203/6250000000000 : ℝ), (3483023700189/25000000000000 : ℝ), (5297744531891/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353651977/10000000000 : ℝ)|^8341 ≤ (2730371808203/6250000000000 : ℝ)^6293
        have hw : |(5353651977/10000000000 : ℝ)|=(5353651977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-452084463/2000000000 : ℝ)|^8341 ≤ (3483023700189/25000000000000 : ℝ)^6293
        have hw : |(-452084463/2000000000 : ℝ)|=(452084463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209305563/400000000 : ℝ)|^8341 ≤ (5297744531891/12500000000000 : ℝ)^6293
        have hw : |(209305563/400000000 : ℝ)|=(209305563/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s3_2 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353652057/10000000000 : ℝ)*x 0 + (5232639139/10000000000 : ℝ)*x 1 + (-565105531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353652057/10000000000 : ℝ)^8341 ≤ (43685949796499/100000000000000 : ℝ)^6293 := by
    have hnat : (5353652057 : ℕ)^8341*100000000000000^6293 ≤ 43685949796499^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353652057 10000000000 43685949796499 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232639139/10000000000 : ℝ)^8341 ≤ (21190978471099/50000000000000 : ℝ)^6293 := by
    have hnat : (5232639139 : ℕ)^8341*50000000000000^6293 ≤ 21190978471099^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232639139 10000000000 21190978471099 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565105531/2500000000 : ℝ)^8341 ≤ (3483023310103/25000000000000 : ℝ)^6293 := by
    have hnat : (565105531 : ℕ)^8341*25000000000000^6293 ≤ 3483023310103^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565105531 2500000000 3483023310103 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353652057/10000000000 : ℝ), (5232639139/10000000000 : ℝ), (-565105531/2500000000 : ℝ)] ![(43685949796499/100000000000000 : ℝ), (21190978471099/50000000000000 : ℝ), (3483023310103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353652057/10000000000 : ℝ)|^8341 ≤ (43685949796499/100000000000000 : ℝ)^6293
        have hw : |(5353652057/10000000000 : ℝ)|=(5353652057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232639139/10000000000 : ℝ)|^8341 ≤ (21190978471099/50000000000000 : ℝ)^6293
        have hw : |(5232639139/10000000000 : ℝ)|=(5232639139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-565105531/2500000000 : ℝ)|^8341 ≤ (3483023310103/25000000000000 : ℝ)^6293
        have hw : |(-565105531/2500000000 : ℝ)|=(565105531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s3_3 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180804309/5000000000 : ℝ)*x 0 + (521351477/1250000000 : ℝ)*x 1 + (570133521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180804309/5000000000 : ℝ)^8341 ≤ (33294535754363/100000000000000 : ℝ)^6293 := by
    have hnat : (2180804309 : ℕ)^8341*100000000000000^6293 ≤ 33294535754363^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180804309 5000000000 33294535754363 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521351477/1250000000 : ℝ)^8341 ≤ (980561506907/3125000000000 : ℝ)^6293 := by
    have hnat : (521351477 : ℕ)^8341*3125000000000^6293 ≤ 980561506907^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521351477 1250000000 980561506907 3125000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570133521/1250000000 : ℝ)^8341 ≤ (35327496007913/100000000000000 : ℝ)^6293 := by
    have hnat : (570133521 : ℕ)^8341*100000000000000^6293 ≤ 35327496007913^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570133521 1250000000 35327496007913 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180804309/5000000000 : ℝ), (521351477/1250000000 : ℝ), (570133521/1250000000 : ℝ)] ![(33294535754363/100000000000000 : ℝ), (980561506907/3125000000000 : ℝ), (35327496007913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180804309/5000000000 : ℝ)|^8341 ≤ (33294535754363/100000000000000 : ℝ)^6293
        have hw : |(2180804309/5000000000 : ℝ)|=(2180804309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521351477/1250000000 : ℝ)|^8341 ≤ (980561506907/3125000000000 : ℝ)^6293
        have hw : |(521351477/1250000000 : ℝ)|=(521351477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(570133521/1250000000 : ℝ)|^8341 ≤ (35327496007913/100000000000000 : ℝ)^6293
        have hw : |(570133521/1250000000 : ℝ)|=(570133521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s3_4 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160300309/10000000000 : ℝ)*x 0 + (2616698247/5000000000 : ℝ)*x 1 + (339237989/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160300309/10000000000 : ℝ)^8341 ≤ (2624023729983/20000000000000 : ℝ)^6293 := by
    have hnat : (2160300309 : ℕ)^8341*20000000000000^6293 ≤ 2624023729983^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160300309 10000000000 2624023729983 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616698247/5000000000 : ℝ)^8341 ≤ (2649380480443/6250000000000 : ℝ)^6293 := by
    have hnat : (2616698247 : ℕ)^8341*6250000000000^6293 ≤ 2649380480443^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616698247 5000000000 2649380480443 6250000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339237989/625000000 : ℝ)^8341 ≤ (22244896826201/50000000000000 : ℝ)^6293 := by
    have hnat : (339237989 : ℕ)^8341*50000000000000^6293 ≤ 22244896826201^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339237989 625000000 22244896826201 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160300309/10000000000 : ℝ), (2616698247/5000000000 : ℝ), (339237989/625000000 : ℝ)] ![(2624023729983/20000000000000 : ℝ), (2649380480443/6250000000000 : ℝ), (22244896826201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160300309/10000000000 : ℝ)|^8341 ≤ (2624023729983/20000000000000 : ℝ)^6293
        have hw : |(-2160300309/10000000000 : ℝ)|=(2160300309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616698247/5000000000 : ℝ)|^8341 ≤ (2649380480443/6250000000000 : ℝ)^6293
        have hw : |(2616698247/5000000000 : ℝ)|=(2616698247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339237989/625000000 : ℝ)|^8341 ≤ (22244896826201/50000000000000 : ℝ)^6293
        have hw : |(339237989/625000000 : ℝ)|=(339237989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s3_5 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (21215969/40000000 : ℝ)*x 0 + (-2065253501/10000000000 : ℝ)*x 1 + (1356951979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21215969/40000000 : ℝ)^8341 ≤ (2696853739209/6250000000000 : ℝ)^6293 := by
    have hnat : (21215969 : ℕ)^8341*6250000000000^6293 ≤ 2696853739209^6293*40000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21215969 40000000 2696853739209 6250000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065253501/10000000000 : ℝ)^8341 ≤ (386267047021/3125000000000 : ℝ)^6293 := by
    have hnat : (2065253501 : ℕ)^8341*3125000000000^6293 ≤ 386267047021^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065253501 10000000000 386267047021 3125000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356951979/2500000000 : ℝ)^8341 ≤ (8897958930381/20000000000000 : ℝ)^6293 := by
    have hnat : (1356951979 : ℕ)^8341*20000000000000^6293 ≤ 8897958930381^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356951979 2500000000 8897958930381 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21215969/40000000 : ℝ), (-2065253501/10000000000 : ℝ), (1356951979/2500000000 : ℝ)] ![(2696853739209/6250000000000 : ℝ), (386267047021/3125000000000 : ℝ), (8897958930381/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21215969/40000000 : ℝ)|^8341 ≤ (2696853739209/6250000000000 : ℝ)^6293
        have hw : |(21215969/40000000 : ℝ)|=(21215969/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065253501/10000000000 : ℝ)|^8341 ≤ (386267047021/3125000000000 : ℝ)^6293
        have hw : |(-2065253501/10000000000 : ℝ)|=(2065253501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356951979/2500000000 : ℝ)|^8341 ≤ (8897958930381/20000000000000 : ℝ)^6293
        have hw : |(1356951979/2500000000 : ℝ)|=(1356951979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s3_6 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303992129/10000000000 : ℝ)*x 0 + (1085561623/2000000000 : ℝ)*x 1 + (-129078337/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303992129/10000000000 : ℝ)^8341 ≤ (8629931704523/20000000000000 : ℝ)^6293 := by
    have hnat : (5303992129 : ℕ)^8341*20000000000000^6293 ≤ 8629931704523^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303992129 10000000000 8629931704523 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085561623/2000000000 : ℝ)^8341 ≤ (22244898406937/50000000000000 : ℝ)^6293 := by
    have hnat : (1085561623 : ℕ)^8341*50000000000000^6293 ≤ 22244898406937^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085561623 2000000000 22244898406937 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129078337/625000000 : ℝ)^8341 ≤ (12360544640001/100000000000000 : ℝ)^6293 := by
    have hnat : (129078337 : ℕ)^8341*100000000000000^6293 ≤ 12360544640001^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129078337 625000000 12360544640001 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303992129/10000000000 : ℝ), (1085561623/2000000000 : ℝ), (-129078337/625000000 : ℝ)] ![(8629931704523/20000000000000 : ℝ), (22244898406937/50000000000000 : ℝ), (12360544640001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303992129/10000000000 : ℝ)|^8341 ≤ (8629931704523/20000000000000 : ℝ)^6293
        have hw : |(5303992129/10000000000 : ℝ)|=(5303992129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085561623/2000000000 : ℝ)|^8341 ≤ (22244898406937/50000000000000 : ℝ)^6293
        have hw : |(1085561623/2000000000 : ℝ)|=(1085561623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129078337/625000000 : ℝ)|^8341 ≤ (12360544640001/100000000000000 : ℝ)^6293
        have hw : |(-129078337/625000000 : ℝ)|=(129078337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s3_7 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174465763/400000000 : ℝ)*x 0 + (4559560067/10000000000 : ℝ)*x 1 + (521541039/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174465763/400000000 : ℝ)^8341 ≤ (33294894502143/100000000000000 : ℝ)^6293 := by
    have hnat : (174465763 : ℕ)^8341*100000000000000^6293 ≤ 33294894502143^6293*400000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174465763 400000000 33294894502143 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4559560067/10000000000 : ℝ)^8341 ≤ (88280036207/250000000000 : ℝ)^6293 := by
    have hnat : (4559560067 : ℕ)^8341*250000000000^6293 ≤ 88280036207^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4559560067 10000000000 88280036207 250000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521541039/1250000000 : ℝ)^8341 ≤ (31393090998933/100000000000000 : ℝ)^6293 := by
    have hnat : (521541039 : ℕ)^8341*100000000000000^6293 ≤ 31393090998933^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521541039 1250000000 31393090998933 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174465763/400000000 : ℝ), (4559560067/10000000000 : ℝ), (521541039/1250000000 : ℝ)] ![(33294894502143/100000000000000 : ℝ), (88280036207/250000000000 : ℝ), (31393090998933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174465763/400000000 : ℝ)|^8341 ≤ (33294894502143/100000000000000 : ℝ)^6293
        have hw : |(174465763/400000000 : ℝ)|=(174465763/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4559560067/10000000000 : ℝ)|^8341 ≤ (88280036207/250000000000 : ℝ)^6293
        have hw : |(4559560067/10000000000 : ℝ)|=(4559560067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521541039/1250000000 : ℝ)|^8341 ≤ (31393090998933/100000000000000 : ℝ)^6293
        have hw : |(521541039/1250000000 : ℝ)|=(521541039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1148_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10653/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14799/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3297/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9097/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3297/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9097/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3297/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9097/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3297/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9097/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3297/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9097/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3297/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9097/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9097/100000 : ℝ) ^ (2085/512 : ℝ) ≤ (5759130322091001/100000000000000000000 : ℝ) := by
    have hpowers : (9097/100000 : ℝ)^2085 ≤ (5759130322091001/100000000000000000000 : ℝ)^512 := by
      have hnat : (9097 : ℕ)^2085*100000000000000000000^512 ≤ 5759130322091001^512*100000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9097 100000 5759130322091001 100000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9097/100000 : ℝ)) (X := (5759130322091001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3297/20000 : ℝ) ^ (2085/512 : ℝ) ≤ (64830332599999461/100000000000000000000 : ℝ) := by
    have hpowers : (3297/20000 : ℝ)^2085 ≤ (64830332599999461/100000000000000000000 : ℝ)^512 := by
      have hnat : (3297 : ℕ)^2085*100000000000000000000^512 ≤ 64830332599999461^512*20000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3297 20000 64830332599999461 100000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3297/20000 : ℝ)) (X := (64830332599999461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005759130322091001/50000000000000000000 : ℝ) ≤ (10000282834207831/10000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (50005759130322091001/50000000000000000000 : ℝ)^512 ≤ (10000282834207831/10000000000000000 : ℝ)^2085 := by
      have hnat : (50005759130322091001 : ℕ)^512*10000000000000000^2085 ≤ 10000282834207831^2085*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005759130322091001 50000000000000000000 10000282834207831 10000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282834207831/10000000000000000 : ℝ)) (X := (50005759130322091001/50000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50035294731461045231/50000000000000000000 : ℝ) ≤ (2500433239631657/2500000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (50035294731461045231/50000000000000000000 : ℝ)^512 ≤ (2500433239631657/2500000000000000 : ℝ)^2085 := by
      have hnat : (50035294731461045231 : ℕ)^512*2500000000000000^2085 ≤ 2500433239631657^2085*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035294731461045231 50000000000000000000 2500433239631657 2500000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500433239631657/2500000000000000 : ℝ)) (X := (50035294731461045231/50000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50064830332599999461/50000000000000000000 : ℝ) ≤ (400127323313817/400000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (50064830332599999461/50000000000000000000 : ℝ)^512 ≤ (400127323313817/400000000000000 : ℝ)^2085 := by
      have hnat : (50064830332599999461 : ℕ)^512*400000000000000^2085 ≤ 400127323313817^2085*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50064830332599999461 50000000000000000000 400127323313817 400000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400127323313817/400000000000000 : ℝ)) (X := (50064830332599999461/50000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5759130322091001/100000000000000000000 : ℝ) ≤ ((7385570601727126281/7388000000000000000 : ℝ)+2*(1450124318797/738800000000000 : ℝ)*(9097/100000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (7385570601727126281/7388000000000000000 : ℝ)+2*(1450124318797/738800000000000 : ℝ)*(9097/100000 : ℝ)=(10000282834207831/10000000000000000 : ℝ) by norm_num, show 1+2*(5759130322091001/100000000000000000000 : ℝ)=(50005759130322091001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64830332599999461/100000000000000000000 : ℝ)+(5759130322091001/100000000000000000000 : ℝ) ≤ ((7385570601727126281/7388000000000000000 : ℝ)+(1450124318797/738800000000000 : ℝ)*((3297/20000 : ℝ)+(9097/100000 : ℝ)))^(2085/512 : ℝ) := by
    rw [show (7385570601727126281/7388000000000000000 : ℝ)+(1450124318797/738800000000000 : ℝ)*((3297/20000 : ℝ)+(9097/100000 : ℝ))=(2500433239631657/2500000000000000 : ℝ) by norm_num, show 1+(64830332599999461/100000000000000000000 : ℝ)+(5759130322091001/100000000000000000000 : ℝ)=(50035294731461045231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64830332599999461/100000000000000000000 : ℝ) ≤ ((7385570601727126281/7388000000000000000 : ℝ)+2*(1450124318797/738800000000000 : ℝ)*(3297/20000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (7385570601727126281/7388000000000000000 : ℝ)+2*(1450124318797/738800000000000 : ℝ)*(3297/20000 : ℝ)=(400127323313817/400000000000000 : ℝ) by norm_num, show 1+2*(64830332599999461/100000000000000000000 : ℝ)=(50064830332599999461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7385570601727126281/7388000000000000000 : ℝ)*(X 1 0+X 2 0)+(1450124318797/738800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (9097/100000 : ℝ)) (hi := (3297/20000 : ℝ)) (c := (7385570601727126281/7388000000000000000 : ℝ)) (alpha := (1450124318797/738800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7385570601727126281/7388000000000000000 : ℝ)*(X 0 1+X 2 1)+(1450124318797/738800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (9097/100000 : ℝ)) (hi := (3297/20000 : ℝ)) (c := (7385570601727126281/7388000000000000000 : ℝ)) (alpha := (1450124318797/738800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7385570601727126281/7388000000000000000 : ℝ)*(X 0 2+X 1 2)+(1450124318797/738800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (9097/100000 : ℝ)) (hi := (3297/20000 : ℝ)) (c := (7385570601727126281/7388000000000000000 : ℝ)) (alpha := (1450124318797/738800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2160282513/10000000000 : ℝ)*X 0 0+(5428569283/10000000000 : ℝ)*X 0 1+(20930557/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353651977/10000000000 : ℝ)*X 1 0+(-452084463/2000000000 : ℝ)*X 1 1+(209305563/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353652057/10000000000 : ℝ)*X 2 0+(5232639139/10000000000 : ℝ)*X 2 1+(-565105531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180804309/5000000000 : ℝ)*X 0 0+(521351477/1250000000 : ℝ)*X 0 1+(570133521/1250000000 : ℝ)*X 0 2+(2180804309/5000000000 : ℝ)*X 1 0+(521351477/1250000000 : ℝ)*X 1 1+(570133521/1250000000 : ℝ)*X 1 2+(2180804309/5000000000 : ℝ)*X 2 0+(521351477/1250000000 : ℝ)*X 2 1+(570133521/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2160300309/10000000000 : ℝ)*X 0 0+(2616698247/5000000000 : ℝ)*X 0 1+(339237989/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((21215969/40000000 : ℝ)*X 1 0+(-2065253501/10000000000 : ℝ)*X 1 1+(1356951979/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303992129/10000000000 : ℝ)*X 2 0+(1085561623/2000000000 : ℝ)*X 2 1+(-129078337/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174465763/400000000 : ℝ)*X 0 0+(4559560067/10000000000 : ℝ)*X 0 1+(521541039/1250000000 : ℝ)*X 0 2+(174465763/400000000 : ℝ)*X 1 0+(4559560067/10000000000 : ℝ)*X 1 1+(521541039/1250000000 : ℝ)*X 1 2+(174465763/400000000 : ℝ)*X 2 0+(4559560067/10000000000 : ℝ)*X 2 1+(521541039/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75235274623196151723356997/46175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164210003/25000000000000 : ℝ)*(base19) + (326386463/50000000000000 : ℝ)*(base23) + (49716423/100000000000000 : ℝ)*(lower2) + (94698043/100000000000000 : ℝ)*(upper5) + (958288919571379/25000000000000 : ℝ)*(major0) + (958288919571379/25000000000000 : ℝ)*(major1) + (1916577839142759/50000000000000 : ℝ)*(major2) + (5103870874076471/100000000000000 : ℝ)*(sp0) + (1020776337068713/20000000000000 : ℝ)*(sp1) + (51038830401999/1000000000000 : ℝ)*(sp2) + (256242322838323/10000000000000 : ℝ)*(sp3) + (2563779271/20000000000000 : ℝ)*(sp4) + (5403157/400000000000 : ℝ)*(sp5) + (547612909/12500000000000 : ℝ)*(sp7) + (2562427609286503/100000000000000 : ℝ)*(f.failure) + (2551941846486413/50000000000000 : ℝ)*(f.sum) + (4333676397631/36940000000000000000000000000 : ℝ)*base66 + (621600808893973501/184700000000000000000000000000000 : ℝ)*base68 + (4832188668085409279/369400000000000000000000000000000 : ℝ)*base69 + (2168865119680573501/184700000000000000000000000000000 : ℝ)*base72 + (267260157900789/36940000000000000000000000000 : ℝ)*base73 + (1316968258501590721/369400000000000000000000000000000 : ℝ)*base76 + (1484673522211058501/184700000000000000000000000000000 : ℝ)*base78 + (1451480561401858501/184700000000000000000000000000000 : ℝ)*base80 + (22154944877623/9235000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (110820867/10000000000000000000000 : ℝ)*base89 + (110820867/10000000000000000000000 : ℝ)*base91 + (89179133/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (884361396270500233773549189/92350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (462867661/25000000000000 : ℝ)*(base19) + (251336503/12500000000000 : ℝ)*(base23) + (46777821/20000000000000 : ℝ)*(upper3) + (21998993/20000000000000 : ℝ)*(lower4) + (192791341/100000000000000 : ℝ)*(upper5) + (965770277613541/25000000000000 : ℝ)*(major0) + (965770277613541/25000000000000 : ℝ)*(major1) + (965770277613541/25000000000000 : ℝ)*(major2) + (1352595311/4000000000000 : ℝ)*(sp1) + (20602005093/50000000000000 : ℝ)*(sp2) + (5143729429570097/100000000000000 : ℝ)*(sp4) + (5143693763216677/100000000000000 : ℝ)*(sp5) + (5143686214867887/100000000000000 : ℝ)*(sp6) + (12912162360659/500000000000 : ℝ)*(sp7) + (12912162360659/500000000000 : ℝ)*(f.failure) + (5143729429570097/100000000000000 : ℝ)*(f.sum) + (2537205136771/1154375000000000000000000000 : ℝ)*base66 + (1722774841750258979/184700000000000000000000000000000 : ℝ)*base68 + (2091286436597258979/184700000000000000000000000000000 : ℝ)*base70 + (1123324325373158979/184700000000000000000000000000000 : ℝ)*base72 + (28821964171853/9235000000000000000000000000 : ℝ)*base74 + (1093945099663558979/184700000000000000000000000000000 : ℝ)*base76 + (1875046786993158979/184700000000000000000000000000000 : ℝ)*base78 + (1383431615952958979/184700000000000000000000000000000 : ℝ)*base80 + (19543315258343/9235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (369951/50000000000000000000 : ℝ)*base89 + (369951/50000000000000000000 : ℝ)*base91 + (369951/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1148_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10653/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14799/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1148_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1148_s4_0 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-270404333/1250000000 : ℝ)*x 0 + (337600557/625000000 : ℝ)*x 1 + (5257668453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270404333/1250000000 : ℝ)^8341 ≤ (13143744782021/100000000000000 : ℝ)^6293 := by
    have hnat : (270404333 : ℕ)^8341*100000000000000^6293 ≤ 13143744782021^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270404333 1250000000 13143744782021 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337600557/625000000 : ℝ)^8341 ≤ (44205388168491/100000000000000 : ℝ)^6293 := by
    have hnat : (337600557 : ℕ)^8341*100000000000000^6293 ≤ 44205388168491^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337600557 625000000 44205388168491 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257668453/10000000000 : ℝ)^8341 ≤ (2665679189289/6250000000000 : ℝ)^6293 := by
    have hnat : (5257668453 : ℕ)^8341*6250000000000^6293 ≤ 2665679189289^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257668453 10000000000 2665679189289 6250000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270404333/1250000000 : ℝ), (337600557/625000000 : ℝ), (5257668453/10000000000 : ℝ)] ![(13143744782021/100000000000000 : ℝ), (44205388168491/100000000000000 : ℝ), (2665679189289/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270404333/1250000000 : ℝ)|^8341 ≤ (13143744782021/100000000000000 : ℝ)^6293
        have hw : |(-270404333/1250000000 : ℝ)|=(270404333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337600557/625000000 : ℝ)|^8341 ≤ (44205388168491/100000000000000 : ℝ)^6293
        have hw : |(337600557/625000000 : ℝ)|=(337600557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257668453/10000000000 : ℝ)|^8341 ≤ (2665679189289/6250000000000 : ℝ)^6293
        have hw : |(5257668453/10000000000 : ℝ)|=(5257668453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s4_1 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267345789/500000000 : ℝ)*x 0 + (-2236379489/10000000000 : ℝ)*x 1 + (2628834409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267345789/500000000 : ℝ)^8341 ≤ (21806553801667/50000000000000 : ℝ)^6293 := by
    have hnat : (267345789 : ℕ)^8341*50000000000000^6293 ≤ 21806553801667^6293*500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267345789 500000000 21806553801667 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236379489/10000000000 : ℝ)^8341 ≤ (13736021429587/100000000000000 : ℝ)^6293 := by
    have hnat : (2236379489 : ℕ)^8341*100000000000000^6293 ≤ 13736021429587^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236379489 10000000000 13736021429587 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628834409/5000000000 : ℝ)^8341 ≤ (10662717738289/25000000000000 : ℝ)^6293 := by
    have hnat : (2628834409 : ℕ)^8341*25000000000000^6293 ≤ 10662717738289^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628834409 5000000000 10662717738289 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267345789/500000000 : ℝ), (-2236379489/10000000000 : ℝ), (2628834409/5000000000 : ℝ)] ![(21806553801667/50000000000000 : ℝ), (13736021429587/100000000000000 : ℝ), (10662717738289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267345789/500000000 : ℝ)|^8341 ≤ (21806553801667/50000000000000 : ℝ)^6293
        have hw : |(267345789/500000000 : ℝ)|=(267345789/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2236379489/10000000000 : ℝ)|^8341 ≤ (13736021429587/100000000000000 : ℝ)^6293
        have hw : |(-2236379489/10000000000 : ℝ)|=(2236379489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628834409/5000000000 : ℝ)|^8341 ≤ (10662717738289/25000000000000 : ℝ)^6293
        have hw : |(2628834409/5000000000 : ℝ)|=(2628834409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s4_2 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346915937/10000000000 : ℝ)*x 0 + (5257668417/10000000000 : ℝ)*x 1 + (-223637981/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346915937/10000000000 : ℝ)^8341 ≤ (43613109300693/100000000000000 : ℝ)^6293 := by
    have hnat : (5346915937 : ℕ)^8341*100000000000000^6293 ≤ 43613109300693^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346915937 10000000000 43613109300693 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257668417/10000000000 : ℝ)^8341 ≤ (42650866641547/100000000000000 : ℝ)^6293 := by
    have hnat : (5257668417 : ℕ)^8341*100000000000000^6293 ≤ 42650866641547^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257668417 10000000000 42650866641547 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223637981/1000000000 : ℝ)^8341 ≤ (3434006010709/25000000000000 : ℝ)^6293 := by
    have hnat : (223637981 : ℕ)^8341*25000000000000^6293 ≤ 3434006010709^6293*1000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223637981 1000000000 3434006010709 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346915937/10000000000 : ℝ), (5257668417/10000000000 : ℝ), (-223637981/1000000000 : ℝ)] ![(43613109300693/100000000000000 : ℝ), (42650866641547/100000000000000 : ℝ), (3434006010709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346915937/10000000000 : ℝ)|^8341 ≤ (43613109300693/100000000000000 : ℝ)^6293
        have hw : |(5346915937/10000000000 : ℝ)|=(5346915937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257668417/10000000000 : ℝ)|^8341 ≤ (42650866641547/100000000000000 : ℝ)^6293
        have hw : |(5257668417/10000000000 : ℝ)|=(5257668417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223637981/1000000000 : ℝ)|^8341 ≤ (3434006010709/25000000000000 : ℝ)^6293
        have hw : |(-223637981/1000000000 : ℝ)|=(223637981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s4_3 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363372499/10000000000 : ℝ)*x 0 + (4222359821/10000000000 : ℝ)*x 1 + (901812681/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363372499/10000000000 : ℝ)^8341 ≤ (33312383547291/100000000000000 : ℝ)^6293 := by
    have hnat : (4363372499 : ℕ)^8341*100000000000000^6293 ≤ 33312383547291^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363372499 10000000000 33312383547291 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222359821/10000000000 : ℝ)^8341 ≤ (31893014907269/100000000000000 : ℝ)^6293 := by
    have hnat : (4222359821 : ℕ)^8341*100000000000000^6293 ≤ 31893014907269^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222359821 10000000000 31893014907269 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901812681/2000000000 : ℝ)^8341 ≤ (34794601528943/100000000000000 : ℝ)^6293 := by
    have hnat : (901812681 : ℕ)^8341*100000000000000^6293 ≤ 34794601528943^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901812681 2000000000 34794601528943 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363372499/10000000000 : ℝ), (4222359821/10000000000 : ℝ), (901812681/2000000000 : ℝ)] ![(33312383547291/100000000000000 : ℝ), (31893014907269/100000000000000 : ℝ), (34794601528943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363372499/10000000000 : ℝ)|^8341 ≤ (33312383547291/100000000000000 : ℝ)^6293
        have hw : |(4363372499/10000000000 : ℝ)|=(4363372499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222359821/10000000000 : ℝ)|^8341 ≤ (31893014907269/100000000000000 : ℝ)^6293
        have hw : |(4222359821/10000000000 : ℝ)|=(4222359821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901812681/2000000000 : ℝ)|^8341 ≤ (34794601528943/100000000000000 : ℝ)^6293
        have hw : |(901812681/2000000000 : ℝ)|=(901812681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s4_4 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-33800659/156250000 : ℝ)*x 0 + (1314519389/2500000000 : ℝ)*x 1 + (2700598901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33800659/156250000 : ℝ)^8341 ≤ (13143805278723/100000000000000 : ℝ)^6293 := by
    have hnat : (33800659 : ℕ)^8341*100000000000000^6293 ≤ 13143805278723^6293*156250000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33800659 156250000 13143805278723 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314519389/2500000000 : ℝ)^8341 ≤ (8531053163707/20000000000000 : ℝ)^6293 := by
    have hnat : (1314519389 : ℕ)^8341*20000000000000^6293 ≤ 8531053163707^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314519389 2500000000 8531053163707 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700598901/5000000000 : ℝ)^8341 ≤ (44200928884587/100000000000000 : ℝ)^6293 := by
    have hnat : (2700598901 : ℕ)^8341*100000000000000^6293 ≤ 44200928884587^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700598901 5000000000 44200928884587 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33800659/156250000 : ℝ), (1314519389/2500000000 : ℝ), (2700598901/5000000000 : ℝ)] ![(13143805278723/100000000000000 : ℝ), (8531053163707/20000000000000 : ℝ), (44200928884587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33800659/156250000 : ℝ)|^8341 ≤ (13143805278723/100000000000000 : ℝ)^6293
        have hw : |(-33800659/156250000 : ℝ)|=(33800659/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314519389/2500000000 : ℝ)|^8341 ≤ (8531053163707/20000000000000 : ℝ)^6293
        have hw : |(1314519389/2500000000 : ℝ)|=(1314519389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700598901/5000000000 : ℝ)|^8341 ≤ (44200928884587/100000000000000 : ℝ)^6293
        have hw : |(2700598901/5000000000 : ℝ)|=(2700598901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s4_5 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062086823/2000000000 : ℝ)*x 0 + (-1046424981/5000000000 : ℝ)*x 1 + (270059887/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062086823/2000000000 : ℝ)^8341 ≤ (10804783856651/25000000000000 : ℝ)^6293 := by
    have hnat : (1062086823 : ℕ)^8341*25000000000000^6293 ≤ 10804783856651^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062086823 2000000000 10804783856651 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046424981/5000000000 : ℝ)^8341 ≤ (12579936351033/100000000000000 : ℝ)^6293 := by
    have hnat : (1046424981 : ℕ)^8341*100000000000000^6293 ≤ 12579936351033^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046424981 5000000000 12579936351033 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270059887/500000000 : ℝ)^8341 ≤ (8840185642417/20000000000000 : ℝ)^6293 := by
    have hnat : (270059887 : ℕ)^8341*20000000000000^6293 ≤ 8840185642417^6293*500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270059887 500000000 8840185642417 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062086823/2000000000 : ℝ), (-1046424981/5000000000 : ℝ), (270059887/500000000 : ℝ)] ![(10804783856651/25000000000000 : ℝ), (12579936351033/100000000000000 : ℝ), (8840185642417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062086823/2000000000 : ℝ)|^8341 ≤ (10804783856651/25000000000000 : ℝ)^6293
        have hw : |(1062086823/2000000000 : ℝ)|=(1062086823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1046424981/5000000000 : ℝ)|^8341 ≤ (12579936351033/100000000000000 : ℝ)^6293
        have hw : |(-1046424981/5000000000 : ℝ)|=(1046424981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270059887/500000000 : ℝ)|^8341 ≤ (8840185642417/20000000000000 : ℝ)^6293
        have hw : |(270059887/500000000 : ℝ)|=(270059887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s4_6 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310434041/10000000000 : ℝ)*x 0 + (5401197727/10000000000 : ℝ)*x 1 + (-1046425039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310434041/10000000000 : ℝ)^8341 ≤ (10804783657089/25000000000000 : ℝ)^6293 := by
    have hnat : (5310434041 : ℕ)^8341*25000000000000^6293 ≤ 10804783657089^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310434041 10000000000 10804783657089 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401197727/10000000000 : ℝ)^8341 ≤ (11050232017769/25000000000000 : ℝ)^6293 := by
    have hnat : (5401197727 : ℕ)^8341*25000000000000^6293 ≤ 11050232017769^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401197727 10000000000 11050232017769 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046425039/5000000000 : ℝ)^8341 ≤ (12579937275217/100000000000000 : ℝ)^6293 := by
    have hnat : (1046425039 : ℕ)^8341*100000000000000^6293 ≤ 12579937275217^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046425039 5000000000 12579937275217 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310434041/10000000000 : ℝ), (5401197727/10000000000 : ℝ), (-1046425039/5000000000 : ℝ)] ![(10804783657089/25000000000000 : ℝ), (11050232017769/25000000000000 : ℝ), (12579937275217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310434041/10000000000 : ℝ)|^8341 ≤ (10804783657089/25000000000000 : ℝ)^6293
        have hw : |(5310434041/10000000000 : ℝ)|=(5310434041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401197727/10000000000 : ℝ)|^8341 ≤ (11050232017769/25000000000000 : ℝ)^6293
        have hw : |(5401197727/10000000000 : ℝ)|=(5401197727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1046425039/5000000000 : ℝ)|^8341 ≤ (12579937275217/100000000000000 : ℝ)^6293
        have hw : |(-1046425039/5000000000 : ℝ)|=(1046425039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s4_7 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363386523/10000000000 : ℝ)*x 0 + (4508247623/10000000000 : ℝ)*x 1 + (2111589503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363386523/10000000000 : ℝ)^8341 ≤ (33312525458251/100000000000000 : ℝ)^6293 := by
    have hnat : (4363386523 : ℕ)^8341*100000000000000^6293 ≤ 33312525458251^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363386523 10000000000 33312525458251 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508247623/10000000000 : ℝ)^8341 ≤ (8696564512151/25000000000000 : ℝ)^6293 := by
    have hnat : (4508247623 : ℕ)^8341*25000000000000^6293 ≤ 8696564512151^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508247623 10000000000 8696564512151 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111589503/5000000000 : ℝ)^8341 ≤ (31901216466509/100000000000000 : ℝ)^6293 := by
    have hnat : (2111589503 : ℕ)^8341*100000000000000^6293 ≤ 31901216466509^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111589503 5000000000 31901216466509 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363386523/10000000000 : ℝ), (4508247623/10000000000 : ℝ), (2111589503/5000000000 : ℝ)] ![(33312525458251/100000000000000 : ℝ), (8696564512151/25000000000000 : ℝ), (31901216466509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363386523/10000000000 : ℝ)|^8341 ≤ (33312525458251/100000000000000 : ℝ)^6293
        have hw : |(4363386523/10000000000 : ℝ)|=(4363386523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508247623/10000000000 : ℝ)|^8341 ≤ (8696564512151/25000000000000 : ℝ)^6293
        have hw : |(4508247623/10000000000 : ℝ)|=(4508247623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111589503/5000000000 : ℝ)|^8341 ≤ (31901216466509/100000000000000 : ℝ)^6293
        have hw : |(2111589503/5000000000 : ℝ)|=(2111589503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1148_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10653/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11187/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14799/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10653/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14799/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10653/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14799/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10653/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14799/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10653/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14799/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10653/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14799/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10653/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (10653/100000 : ℝ) ^ (2085/512 : ℝ) ≤ (10954873300613707/100000000000000000000 : ℝ) := by
    have hpowers : (10653/100000 : ℝ)^2085 ≤ (10954873300613707/100000000000000000000 : ℝ)^512 := by
      have hnat : (10653 : ℕ)^2085*100000000000000000000^512 ≤ 10954873300613707^512*100000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10653 100000 10954873300613707 100000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10653/100000 : ℝ)) (X := (10954873300613707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14799/100000 : ℝ) ^ (2085/512 : ℝ) ≤ (2088987343266477/5000000000000000000 : ℝ) := by
    have hpowers : (14799/100000 : ℝ)^2085 ≤ (2088987343266477/5000000000000000000 : ℝ)^512 := by
      have hnat : (14799 : ℕ)^2085*5000000000000000000^512 ≤ 2088987343266477^512*100000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14799 100000 2088987343266477 5000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14799/100000 : ℝ)) (X := (2088987343266477/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010954873300613707/50000000000000000000 : ℝ) ≤ (10000537979053029/10000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (50010954873300613707/50000000000000000000 : ℝ)^512 ≤ (10000537979053029/10000000000000000 : ℝ)^2085 := by
      have hnat : (50010954873300613707 : ℕ)^512*10000000000000000^2085 ≤ 10000537979053029^2085*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010954873300613707 50000000000000000000 10000537979053029 10000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537979053029/10000000000000000 : ℝ)) (X := (50010954873300613707/50000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052734620165943247/100000000000000000000 : ℝ) ≤ (10001294712527177/10000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (100052734620165943247/100000000000000000000 : ℝ)^512 ≤ (10001294712527177/10000000000000000 : ℝ)^2085 := by
      have hnat : (100052734620165943247 : ℕ)^512*10000000000000000^2085 ≤ 10001294712527177^2085*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052734620165943247 100000000000000000000 10001294712527177 10000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001294712527177/10000000000000000 : ℝ)) (X := (100052734620165943247/100000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502088987343266477/2500000000000000000 : ℝ) ≤ (400082057840053/400000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (2502088987343266477/2500000000000000000 : ℝ)^512 ≤ (400082057840053/400000000000000 : ℝ)^2085 := by
      have hnat : (2502088987343266477 : ℕ)^512*400000000000000^2085 ≤ 400082057840053^2085*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502088987343266477 2500000000000000000 400082057840053 400000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400082057840053/400000000000000 : ℝ)) (X := (2502088987343266477/2500000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10954873300613707/100000000000000000000 : ℝ) ≤ ((6907684582958943491/6910000000000000000 : ℝ)+2*(189183368537/103650000000000 : ℝ)*(10653/100000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (6907684582958943491/6910000000000000000 : ℝ)+2*(189183368537/103650000000000 : ℝ)*(10653/100000 : ℝ)=(10000537979053029/10000000000000000 : ℝ) by norm_num, show 1+2*(10954873300613707/100000000000000000000 : ℝ)=(50010954873300613707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2088987343266477/5000000000000000000 : ℝ)+(10954873300613707/100000000000000000000 : ℝ) ≤ ((6907684582958943491/6910000000000000000 : ℝ)+(189183368537/103650000000000 : ℝ)*((14799/100000 : ℝ)+(10653/100000 : ℝ)))^(2085/512 : ℝ) := by
    rw [show (6907684582958943491/6910000000000000000 : ℝ)+(189183368537/103650000000000 : ℝ)*((14799/100000 : ℝ)+(10653/100000 : ℝ))=(10001294712527177/10000000000000000 : ℝ) by norm_num, show 1+(2088987343266477/5000000000000000000 : ℝ)+(10954873300613707/100000000000000000000 : ℝ)=(100052734620165943247/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2088987343266477/5000000000000000000 : ℝ) ≤ ((6907684582958943491/6910000000000000000 : ℝ)+2*(189183368537/103650000000000 : ℝ)*(14799/100000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (6907684582958943491/6910000000000000000 : ℝ)+2*(189183368537/103650000000000 : ℝ)*(14799/100000 : ℝ)=(400082057840053/400000000000000 : ℝ) by norm_num, show 1+2*(2088987343266477/5000000000000000000 : ℝ)=(2502088987343266477/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6907684582958943491/6910000000000000000 : ℝ)*(X 1 0+X 2 0)+(189183368537/103650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (10653/100000 : ℝ)) (hi := (14799/100000 : ℝ)) (c := (6907684582958943491/6910000000000000000 : ℝ)) (alpha := (189183368537/103650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6907684582958943491/6910000000000000000 : ℝ)*(X 0 1+X 2 1)+(189183368537/103650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (10653/100000 : ℝ)) (hi := (14799/100000 : ℝ)) (c := (6907684582958943491/6910000000000000000 : ℝ)) (alpha := (189183368537/103650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6907684582958943491/6910000000000000000 : ℝ)*(X 0 2+X 1 2)+(189183368537/103650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (10653/100000 : ℝ)) (hi := (14799/100000 : ℝ)) (c := (6907684582958943491/6910000000000000000 : ℝ)) (alpha := (189183368537/103650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-270404333/1250000000 : ℝ)*X 0 0+(337600557/625000000 : ℝ)*X 0 1+(5257668453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267345789/500000000 : ℝ)*X 1 0+(-2236379489/10000000000 : ℝ)*X 1 1+(2628834409/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346915937/10000000000 : ℝ)*X 2 0+(5257668417/10000000000 : ℝ)*X 2 1+(-223637981/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363372499/10000000000 : ℝ)*X 0 0+(4222359821/10000000000 : ℝ)*X 0 1+(901812681/2000000000 : ℝ)*X 0 2+(4363372499/10000000000 : ℝ)*X 1 0+(4222359821/10000000000 : ℝ)*X 1 1+(901812681/2000000000 : ℝ)*X 1 2+(4363372499/10000000000 : ℝ)*X 2 0+(4222359821/10000000000 : ℝ)*X 2 1+(901812681/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-33800659/156250000 : ℝ)*X 0 0+(1314519389/2500000000 : ℝ)*X 0 1+(2700598901/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062086823/2000000000 : ℝ)*X 1 0+(-1046424981/5000000000 : ℝ)*X 1 1+(270059887/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310434041/10000000000 : ℝ)*X 2 0+(5401197727/10000000000 : ℝ)*X 2 1+(-1046425039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363386523/10000000000 : ℝ)*X 0 0+(4508247623/10000000000 : ℝ)*X 0 1+(2111589503/5000000000 : ℝ)*X 0 2+(4363386523/10000000000 : ℝ)*X 1 0+(4508247623/10000000000 : ℝ)*X 1 1+(2111589503/5000000000 : ℝ)*X 1 2+(4363386523/10000000000 : ℝ)*X 2 0+(4508247623/10000000000 : ℝ)*X 2 1+(2111589503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (526166654316347292056830009/86375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9048881/6250000000000 : ℝ)*(base15) + (112864169/100000000000000 : ℝ)*(lower2) + (20415491/20000000000000 : ℝ)*(upper3) + (59184461/50000000000000 : ℝ)*(lower4) + (5217636732688667/100000000000000 : ℝ)*(major0) + (5217636732688667/100000000000000 : ℝ)*(major1) + (1304409183172167/25000000000000 : ℝ)*(major2) + (6947328166397213/100000000000000 : ℝ)*(sp0) + (868416659175489/12500000000000 : ℝ)*(sp1) + (6947320477641851/100000000000000 : ℝ)*(sp2) + (54498918554603/1562500000000 : ℝ)*(sp3) + (1312947199/25000000000000 : ℝ)*(sp4) + (6470272079/50000000000000 : ℝ)*(sp6) + (4528320789/50000000000000 : ℝ)*(sp7) + (348793984413617/10000000000000 : ℝ)*(f.failure) + (868416677273251/12500000000000 : ℝ)*(f.sum) + (11937962250077/2073000000000000000000000000 : ℝ)*base65 + (2104762241085516497/691000000000000000000000000000000 : ℝ)*base67 + (5280490456600744991/518250000000000000000000000000000 : ℝ)*base69 + (4822929521221516497/691000000000000000000000000000000 : ℝ)*base71 + (126238870751/414600000000000000000000000 : ℝ)*base74 + (3279543720636994991/518250000000000000000000000000000 : ℝ)*base75 + (5491470546907850509/2073000000000000000000000000000000 : ℝ)*base78 + (4503614097223850509/2073000000000000000000000000000000 : ℝ)*base80 + (3851675205887/2591250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (626187/1000000000000000000000 : ℝ)*base90 + (626187/1000000000000000000000 : ℝ)*base92 + (10626187/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (517106355364229634975133217/86375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1916078577/100000000000000 : ℝ)*(base19) + (1946305787/100000000000000 : ℝ)*(base23) + (97684439/100000000000000 : ℝ)*(upper2) + (5257481/5000000000000 : ℝ)*(upper3) + (282530113/100000000000000 : ℝ)*(upper5) + (1311882289843843/25000000000000 : ℝ)*(major0) + (1311882289843843/25000000000000 : ℝ)*(major1) + (1311882289843843/25000000000000 : ℝ)*(major2) + (51048720979/100000000000000 : ℝ)*(sp1) + (42844961777/100000000000000 : ℝ)*(sp2) + (6987135476057037/100000000000000 : ℝ)*(sp4) + (6987082511257481/100000000000000 : ℝ)*(sp5) + (6987090684789473/100000000000000 : ℝ)*(sp6) + (438490330391881/12500000000000 : ℝ)*(sp7) + (438490330391881/12500000000000 : ℝ)*(f.failure) + (6987135476057037/100000000000000 : ℝ)*(f.sum) + (1082771919361/323906250000000000000000000 : ℝ)*base66 + (2986178208194972261/518250000000000000000000000000000 : ℝ)*base68 + (1562691856564472261/518250000000000000000000000000000 : ℝ)*base70 + (9137918978469722261/518250000000000000000000000000000 : ℝ)*base72 + (65693206641913/10365000000000000000000000000 : ℝ)*base73 + (1114402024420472261/518250000000000000000000000000000 : ℝ)*base76 + (11133843546472472261/518250000000000000000000000000000 : ℝ)*base78 + (872061967565972261/518250000000000000000000000000000 : ℝ)*base80 + (11011592884721/1295625000000000000000000000 : ℝ)*base81 + (7984109/1250000000000000000000 : ℝ)*base89 + (7984109/1250000000000000000000 : ℝ)*base91 + (7984109/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1148_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10653/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1148_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1148_s5_0 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-135241251/625000000 : ℝ)*x 0 + (168586149/312500000 : ℝ)*x 1 + (1316027493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135241251/625000000 : ℝ)^8341 ≤ (13148781189311/100000000000000 : ℝ)^6293 := by
    have hnat : (135241251 : ℕ)^8341*100000000000000^6293 ≤ 13148781189311^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135241251 625000000 13148781189311 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168586149/312500000 : ℝ)^8341 ≤ (11032769456567/25000000000000 : ℝ)^6293 := by
    have hnat : (168586149 : ℕ)^8341*25000000000000^6293 ≤ 11032769456567^6293*312500000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168586149 312500000 11032769456567 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316027493/2500000000 : ℝ)^8341 ≤ (10680035242507/25000000000000 : ℝ)^6293 := by
    have hnat : (1316027493 : ℕ)^8341*25000000000000^6293 ≤ 10680035242507^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316027493 2500000000 10680035242507 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135241251/625000000 : ℝ), (168586149/312500000 : ℝ), (1316027493/2500000000 : ℝ)] ![(13148781189311/100000000000000 : ℝ), (11032769456567/25000000000000 : ℝ), (10680035242507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135241251/625000000 : ℝ)|^8341 ≤ (13148781189311/100000000000000 : ℝ)^6293
        have hw : |(-135241251/625000000 : ℝ)|=(135241251/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168586149/312500000 : ℝ)|^8341 ≤ (11032769456567/25000000000000 : ℝ)^6293
        have hw : |(168586149/312500000 : ℝ)|=(168586149/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316027493/2500000000 : ℝ)|^8341 ≤ (10680035242507/25000000000000 : ℝ)^6293
        have hw : |(1316027493/2500000000 : ℝ)|=(1316027493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s5_1 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672598149/5000000000 : ℝ)*x 0 + (-2230151243/10000000000 : ℝ)*x 1 + (329006871/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672598149/5000000000 : ℝ)^8341 ≤ (21797259452391/50000000000000 : ℝ)^6293 := by
    have hnat : (2672598149 : ℕ)^8341*50000000000000^6293 ≤ 21797259452391^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672598149 5000000000 21797259452391 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2230151243/10000000000 : ℝ)^8341 ≤ (13685340493409/100000000000000 : ℝ)^6293 := by
    have hnat : (2230151243 : ℕ)^8341*100000000000000^6293 ≤ 13685340493409^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230151243 10000000000 13685340493409 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329006871/625000000 : ℝ)^8341 ≤ (42720140582797/100000000000000 : ℝ)^6293 := by
    have hnat : (329006871 : ℕ)^8341*100000000000000^6293 ≤ 42720140582797^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329006871 625000000 42720140582797 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672598149/5000000000 : ℝ), (-2230151243/10000000000 : ℝ), (329006871/625000000 : ℝ)] ![(21797259452391/50000000000000 : ℝ), (13685340493409/100000000000000 : ℝ), (42720140582797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672598149/5000000000 : ℝ)|^8341 ≤ (21797259452391/50000000000000 : ℝ)^6293
        have hw : |(2672598149/5000000000 : ℝ)|=(2672598149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2230151243/10000000000 : ℝ)|^8341 ≤ (13685340493409/100000000000000 : ℝ)^6293
        have hw : |(-2230151243/10000000000 : ℝ)|=(2230151243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329006871/625000000 : ℝ)|^8341 ≤ (42720140582797/100000000000000 : ℝ)^6293
        have hw : |(329006871/625000000 : ℝ)|=(329006871/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s5_2 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668149543/1250000000 : ℝ)*x 0 + (5264109909/10000000000 : ℝ)*x 1 + (-2230151219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668149543/1250000000 : ℝ)^8341 ≤ (21797259701023/50000000000000 : ℝ)^6293 := by
    have hnat : (668149543 : ℕ)^8341*50000000000000^6293 ≤ 21797259701023^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668149543 1250000000 21797259701023 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264109909/10000000000 : ℝ)^8341 ≤ (42720140292373/100000000000000 : ℝ)^6293 := by
    have hnat : (5264109909 : ℕ)^8341*100000000000000^6293 ≤ 42720140292373^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264109909 10000000000 42720140292373 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230151219/10000000000 : ℝ)^8341 ≤ (13685340298203/100000000000000 : ℝ)^6293 := by
    have hnat : (2230151219 : ℕ)^8341*100000000000000^6293 ≤ 13685340298203^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230151219 10000000000 13685340298203 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668149543/1250000000 : ℝ), (5264109909/10000000000 : ℝ), (-2230151219/10000000000 : ℝ)] ![(21797259701023/50000000000000 : ℝ), (42720140292373/100000000000000 : ℝ), (13685340298203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668149543/1250000000 : ℝ)|^8341 ≤ (21797259701023/50000000000000 : ℝ)^6293
        have hw : |(668149543/1250000000 : ℝ)|=(668149543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264109909/10000000000 : ℝ)|^8341 ≤ (42720140292373/100000000000000 : ℝ)^6293
        have hw : |(5264109909/10000000000 : ℝ)|=(5264109909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230151219/10000000000 : ℝ)|^8341 ≤ (13685340298203/100000000000000 : ℝ)^6293
        have hw : |(-2230151219/10000000000 : ℝ)|=(2230151219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s5_3 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (109093423/250000000 : ℝ)*x 0 + (4235552131/10000000000 : ℝ)*x 1 + (899155333/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109093423/250000000 : ℝ)^8341 ≤ (4164508903281/12500000000000 : ℝ)^6293 := by
    have hnat : (109093423 : ℕ)^8341*12500000000000^6293 ≤ 4164508903281^6293*250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109093423 250000000 4164508903281 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235552131/10000000000 : ℝ)^8341 ≤ (16012578648819/50000000000000 : ℝ)^6293 := by
    have hnat : (4235552131 : ℕ)^8341*50000000000000^6293 ≤ 16012578648819^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235552131 10000000000 16012578648819 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899155333/2000000000 : ℝ)^8341 ≤ (8664692864649/25000000000000 : ℝ)^6293 := by
    have hnat : (899155333 : ℕ)^8341*25000000000000^6293 ≤ 8664692864649^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899155333 2000000000 8664692864649 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109093423/250000000 : ℝ), (4235552131/10000000000 : ℝ), (899155333/2000000000 : ℝ)] ![(4164508903281/12500000000000 : ℝ), (16012578648819/50000000000000 : ℝ), (8664692864649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109093423/250000000 : ℝ)|^8341 ≤ (4164508903281/12500000000000 : ℝ)^6293
        have hw : |(109093423/250000000 : ℝ)|=(109093423/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235552131/10000000000 : ℝ)|^8341 ≤ (16012578648819/50000000000000 : ℝ)^6293
        have hw : |(4235552131/10000000000 : ℝ)|=(4235552131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899155333/2000000000 : ℝ)|^8341 ≤ (8664692864649/25000000000000 : ℝ)^6293
        have hw : |(899155333/2000000000 : ℝ)|=(899155333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s5_4 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163865333/10000000000 : ℝ)*x 0 + (2632223679/5000000000 : ℝ)*x 1 + (2697209053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163865333/10000000000 : ℝ)^8341 ≤ (13148824012949/100000000000000 : ℝ)^6293 := by
    have hnat : (2163865333 : ℕ)^8341*100000000000000^6293 ≤ 13148824012949^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163865333 10000000000 13148824012949 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632223679/5000000000 : ℝ)^8341 ≤ (8544754015283/20000000000000 : ℝ)^6293 := by
    have hnat : (2632223679 : ℕ)^8341*20000000000000^6293 ≤ 8544754015283^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632223679 5000000000 8544754015283 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697209053/5000000000 : ℝ)^8341 ≤ (44127405890397/100000000000000 : ℝ)^6293 := by
    have hnat : (2697209053 : ℕ)^8341*100000000000000^6293 ≤ 44127405890397^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697209053 5000000000 44127405890397 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163865333/10000000000 : ℝ), (2632223679/5000000000 : ℝ), (2697209053/5000000000 : ℝ)] ![(13148824012949/100000000000000 : ℝ), (8544754015283/20000000000000 : ℝ), (44127405890397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163865333/10000000000 : ℝ)|^8341 ≤ (13148824012949/100000000000000 : ℝ)^6293
        have hw : |(-2163865333/10000000000 : ℝ)|=(2163865333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632223679/5000000000 : ℝ)|^8341 ≤ (8544754015283/20000000000000 : ℝ)^6293
        have hw : |(2632223679/5000000000 : ℝ)|=(2632223679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697209053/5000000000 : ℝ)|^8341 ≤ (44127405890397/100000000000000 : ℝ)^6293
        have hw : |(2697209053/5000000000 : ℝ)|=(2697209053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s5_5 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656041057/5000000000 : ℝ)*x 0 + (-1049921481/5000000000 : ℝ)*x 1 + (2697209051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656041057/5000000000 : ℝ)^8341 ≤ (43236913525253/100000000000000 : ℝ)^6293 := by
    have hnat : (2656041057 : ℕ)^8341*100000000000000^6293 ≤ 43236913525253^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656041057 5000000000 43236913525253 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049921481/5000000000 : ℝ)^8341 ≤ (505427224449/4000000000000 : ℝ)^6293 := by
    have hnat : (1049921481 : ℕ)^8341*4000000000000^6293 ≤ 505427224449^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049921481 5000000000 505427224449 4000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697209051/5000000000 : ℝ)^8341 ≤ (11031851461757/25000000000000 : ℝ)^6293 := by
    have hnat : (2697209051 : ℕ)^8341*25000000000000^6293 ≤ 11031851461757^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697209051 5000000000 11031851461757 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656041057/5000000000 : ℝ), (-1049921481/5000000000 : ℝ), (2697209051/5000000000 : ℝ)] ![(43236913525253/100000000000000 : ℝ), (505427224449/4000000000000 : ℝ), (11031851461757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656041057/5000000000 : ℝ)|^8341 ≤ (43236913525253/100000000000000 : ℝ)^6293
        have hw : |(2656041057/5000000000 : ℝ)|=(2656041057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049921481/5000000000 : ℝ)|^8341 ≤ (505427224449/4000000000000 : ℝ)^6293
        have hw : |(-1049921481/5000000000 : ℝ)|=(1049921481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697209051/5000000000 : ℝ)|^8341 ≤ (11031851461757/25000000000000 : ℝ)^6293
        have hw : |(2697209051/5000000000 : ℝ)|=(2697209051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s5_6 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656041059/5000000000 : ℝ)*x 0 + (53944181/100000000 : ℝ)*x 1 + (-26248037/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656041059/5000000000 : ℝ)^8341 ≤ (21618456784203/50000000000000 : ℝ)^6293 := by
    have hnat : (2656041059 : ℕ)^8341*50000000000000^6293 ≤ 21618456784203^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656041059 5000000000 21618456784203 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53944181/100000000 : ℝ)^8341 ≤ (44127405825343/100000000000000 : ℝ)^6293 := by
    have hnat : (53944181 : ℕ)^8341*100000000000000^6293 ≤ 44127405825343^6293*100000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53944181 100000000 44127405825343 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26248037/125000000 : ℝ)^8341 ≤ (12635680595273/100000000000000 : ℝ)^6293 := by
    have hnat : (26248037 : ℕ)^8341*100000000000000^6293 ≤ 12635680595273^6293*125000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26248037 125000000 12635680595273 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656041059/5000000000 : ℝ), (53944181/100000000 : ℝ), (-26248037/125000000 : ℝ)] ![(21618456784203/50000000000000 : ℝ), (44127405825343/100000000000000 : ℝ), (12635680595273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656041059/5000000000 : ℝ)|^8341 ≤ (21618456784203/50000000000000 : ℝ)^6293
        have hw : |(2656041059/5000000000 : ℝ)|=(2656041059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53944181/100000000 : ℝ)|^8341 ≤ (44127405825343/100000000000000 : ℝ)^6293
        have hw : |(53944181/100000000 : ℝ)|=(53944181/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26248037/125000000 : ℝ)|^8341 ≤ (12635680595273/100000000000000 : ℝ)^6293
        have hw : |(-26248037/125000000 : ℝ)|=(26248037/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s5_7 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363747499/10000000000 : ℝ)*x 0 + (2247552259/5000000000 : ℝ)*x 1 + (4236226731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363747499/10000000000 : ℝ)^8341 ≤ (33316178279631/100000000000000 : ℝ)^6293 := by
    have hnat : (4363747499 : ℕ)^8341*100000000000000^6293 ≤ 33316178279631^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363747499 10000000000 33316178279631 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247552259/5000000000 : ℝ)^8341 ≤ (17325951790679/50000000000000 : ℝ)^6293 := by
    have hnat : (2247552259 : ℕ)^8341*50000000000000^6293 ≤ 17325951790679^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247552259 5000000000 17325951790679 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236226731/10000000000 : ℝ)^8341 ≤ (3203191811527/10000000000000 : ℝ)^6293 := by
    have hnat : (4236226731 : ℕ)^8341*10000000000000^6293 ≤ 3203191811527^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236226731 10000000000 3203191811527 10000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363747499/10000000000 : ℝ), (2247552259/5000000000 : ℝ), (4236226731/10000000000 : ℝ)] ![(33316178279631/100000000000000 : ℝ), (17325951790679/50000000000000 : ℝ), (3203191811527/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363747499/10000000000 : ℝ)|^8341 ≤ (33316178279631/100000000000000 : ℝ)^6293
        have hw : |(4363747499/10000000000 : ℝ)|=(4363747499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247552259/5000000000 : ℝ)|^8341 ≤ (17325951790679/50000000000000 : ℝ)^6293
        have hw : |(2247552259/5000000000 : ℝ)|=(2247552259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236226731/10000000000 : ℝ)|^8341 ≤ (3203191811527/10000000000000 : ℝ)^6293
        have hw : |(4236226731/10000000000 : ℝ)|=(4236226731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1148_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2831/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14091/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11187/100000 : ℝ) ^ (2085/512 : ℝ) ≤ (6684658928738283/50000000000000000000 : ℝ) := by
    have hpowers : (11187/100000 : ℝ)^2085 ≤ (6684658928738283/50000000000000000000 : ℝ)^512 := by
      have hnat : (11187 : ℕ)^2085*50000000000000000000^512 ≤ 6684658928738283^512*100000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11187 100000 6684658928738283 50000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11187/100000 : ℝ)) (X := (6684658928738283/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (2085/512 : ℝ) ≤ (7133074010105457/20000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^2085 ≤ (7133074010105457/20000000000000000000 : ℝ)^512 := by
      have hnat : (2847 : ℕ)^2085*20000000000000000000^512 ≤ 7133074010105457^512*20000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 7133074010105457 20000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (7133074010105457/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006684658928738283/25000000000000000000 : ℝ) ≤ (5000328268605973/5000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (25006684658928738283/25000000000000000000 : ℝ)^512 ≤ (5000328268605973/5000000000000000 : ℝ)^2085 := by
      have hnat : (25006684658928738283 : ℕ)^512*5000000000000000^2085 ≤ 5000328268605973^2085*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006684658928738283 25000000000000000000 5000328268605973 5000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000328268605973/5000000000000000 : ℝ)) (X := (25006684658928738283/25000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049034687908003851/100000000000000000000 : ℝ) ≤ (1000120389054117/1000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (100049034687908003851/100000000000000000000 : ℝ)^512 ≤ (1000120389054117/1000000000000000 : ℝ)^2085 := by
      have hnat : (100049034687908003851 : ℕ)^512*1000000000000000^2085 ≤ 1000120389054117^2085*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049034687908003851 100000000000000000000 1000120389054117 1000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000120389054117/1000000000000000 : ℝ)) (X := (100049034687908003851/100000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007133074010105457/10000000000000000000 : ℝ) ≤ (5000875621935197/5000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (10007133074010105457/10000000000000000000 : ℝ)^512 ≤ (5000875621935197/5000000000000000 : ℝ)^2085 := by
      have hnat : (10007133074010105457 : ℕ)^512*5000000000000000^2085 ≤ 5000875621935197^2085*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007133074010105457 10000000000000000000 5000875621935197 5000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000875621935197/5000000000000000 : ℝ)) (X := (10007133074010105457/10000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6684658928738283/50000000000000000000 : ℝ) ≤ ((317393277521187017/317500000000000000 : ℝ)+2*(68419166153/38100000000000 : ℝ)*(11187/100000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (317393277521187017/317500000000000000 : ℝ)+2*(68419166153/38100000000000 : ℝ)*(11187/100000 : ℝ)=(5000328268605973/5000000000000000 : ℝ) by norm_num, show 1+2*(6684658928738283/50000000000000000000 : ℝ)=(25006684658928738283/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7133074010105457/20000000000000000000 : ℝ)+(6684658928738283/50000000000000000000 : ℝ) ≤ ((317393277521187017/317500000000000000 : ℝ)+(68419166153/38100000000000 : ℝ)*((2847/20000 : ℝ)+(11187/100000 : ℝ)))^(2085/512 : ℝ) := by
    rw [show (317393277521187017/317500000000000000 : ℝ)+(68419166153/38100000000000 : ℝ)*((2847/20000 : ℝ)+(11187/100000 : ℝ))=(1000120389054117/1000000000000000 : ℝ) by norm_num, show 1+(7133074010105457/20000000000000000000 : ℝ)+(6684658928738283/50000000000000000000 : ℝ)=(100049034687908003851/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7133074010105457/20000000000000000000 : ℝ) ≤ ((317393277521187017/317500000000000000 : ℝ)+2*(68419166153/38100000000000 : ℝ)*(2847/20000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (317393277521187017/317500000000000000 : ℝ)+2*(68419166153/38100000000000 : ℝ)*(2847/20000 : ℝ)=(5000875621935197/5000000000000000 : ℝ) by norm_num, show 1+2*(7133074010105457/20000000000000000000 : ℝ)=(10007133074010105457/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (317393277521187017/317500000000000000 : ℝ)*(X 1 0+X 2 0)+(68419166153/38100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (317393277521187017/317500000000000000 : ℝ)) (alpha := (68419166153/38100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (317393277521187017/317500000000000000 : ℝ)*(X 0 1+X 2 1)+(68419166153/38100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (317393277521187017/317500000000000000 : ℝ)) (alpha := (68419166153/38100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (317393277521187017/317500000000000000 : ℝ)*(X 0 2+X 1 2)+(68419166153/38100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (317393277521187017/317500000000000000 : ℝ)) (alpha := (68419166153/38100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-135241251/625000000 : ℝ)*X 0 0+(168586149/312500000 : ℝ)*X 0 1+(1316027493/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672598149/5000000000 : ℝ)*X 1 0+(-2230151243/10000000000 : ℝ)*X 1 1+(329006871/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668149543/1250000000 : ℝ)*X 2 0+(5264109909/10000000000 : ℝ)*X 2 1+(-2230151219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((109093423/250000000 : ℝ)*X 0 0+(4235552131/10000000000 : ℝ)*X 0 1+(899155333/2000000000 : ℝ)*X 0 2+(109093423/250000000 : ℝ)*X 1 0+(4235552131/10000000000 : ℝ)*X 1 1+(899155333/2000000000 : ℝ)*X 1 2+(109093423/250000000 : ℝ)*X 2 0+(4235552131/10000000000 : ℝ)*X 2 1+(899155333/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2163865333/10000000000 : ℝ)*X 0 0+(2632223679/5000000000 : ℝ)*X 0 1+(2697209053/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656041057/5000000000 : ℝ)*X 1 0+(-1049921481/5000000000 : ℝ)*X 1 1+(2697209051/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656041059/5000000000 : ℝ)*X 2 0+(53944181/100000000 : ℝ)*X 2 1+(-26248037/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363747499/10000000000 : ℝ)*X 0 0+(2247552259/5000000000 : ℝ)*X 0 1+(4236226731/10000000000 : ℝ)*X 0 2+(4363747499/10000000000 : ℝ)*X 1 0+(2247552259/5000000000 : ℝ)*X 1 1+(4236226731/10000000000 : ℝ)*X 1 2+(4363747499/10000000000 : ℝ)*X 2 0+(2247552259/5000000000 : ℝ)*X 2 1+(4236226731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7185677697851808311887693/992187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1050442533/100000000000000 : ℝ)*(base19) + (1014470983/100000000000000 : ℝ)*(base23) + (54437159/100000000000000 : ℝ)*(lower2) + (70381667/50000000000000 : ℝ)*(upper3) + (115969621/100000000000000 : ℝ)*(upper5) + (5748568850925689/100000000000000 : ℝ)*(major0) + (5748568850925689/100000000000000 : ℝ)*(major1) + (574856885092569/10000000000000 : ℝ)*(major2) + (765424935476543/10000000000000 : ℝ)*(sp0) + (1530854712879407/20000000000000 : ℝ)*(sp1) + (1530854720073717/20000000000000 : ℝ)*(sp2) + (768569662317723/20000000000000 : ℝ)*(sp3) + (12630037069/50000000000000 : ℝ)*(sp4) + (14534014591/100000000000000 : ℝ)*(sp7) + (3842862845603207/100000000000000 : ℝ)*(f.failure) + (478392163427473/6250000000000 : ℝ)*(f.sum) + (7296313261237/3810000000000000000000000000 : ℝ)*base65 + (221728854723920287/31750000000000000000000000000000 : ℝ)*base68 + (116475049591372519/9525000000000000000000000000000 : ℝ)*base69 + (511575614119920287/31750000000000000000000000000000 : ℝ)*base72 + (11026199160607/3810000000000000000000000000 : ℝ)*base73 + (87147296728072519/9525000000000000000000000000000 : ℝ)*base75 + (727791187666085861/95250000000000000000000000000000 : ℝ)*base78 + (583805812600835861/95250000000000000000000000000000 : ℝ)*base80 + (671050075139/238125000000000000000000000 : ℝ)*base81 + (16060323/10000000000000000000000 : ℝ)*base89 + (16060323/10000000000000000000000 : ℝ)*base91 + (83939677/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62865274348501044188905011/15875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186892543/25000000000000 : ℝ)*(base19) + (812432697/100000000000000 : ℝ)*(base23) + (1631131/2000000000000 : ℝ)*(upper3) + (6584019/25000000000000 : ℝ)*(lower4) + (41283897/50000000000000 : ℝ)*(upper5) + (5778432449485961/100000000000000 : ℝ)*(major0) + (5778432449485961/100000000000000 : ℝ)*(major1) + (5778432449485961/100000000000000 : ℝ)*(major2) + (19927024289/100000000000000 : ℝ)*(sp1) + (2144955153/10000000000000 : ℝ)*(sp2) + (7694038393693789/100000000000000 : ℝ)*(sp4) + (120219026860927/1562500000000 : ℝ)*(sp5) + (3847008065854781/50000000000000 : ℝ)*(sp6) + (1931413186638771/50000000000000 : ℝ)*(sp7) + (1931413186638771/50000000000000 : ℝ)*(f.failure) + (7694038393693789/100000000000000 : ℝ)*(f.sum) + (34378825213/7441406250000000000000000 : ℝ)*base65 + (2214829887722769989/95250000000000000000000000000000 : ℝ)*base68 + (1892572907587269989/95250000000000000000000000000000 : ℝ)*base70 + (208018191958730011/95250000000000000000000000000000 : ℝ)*base71 + (1454247628579/238125000000000000000000000 : ℝ)*base74 + (2762789035388769989/95250000000000000000000000000000 : ℝ)*base76 + (256755986088230011/95250000000000000000000000000000 : ℝ)*base77 + (1882685851859769989/95250000000000000000000000000000 : ℝ)*base80 + (7203968432173/1905000000000000000000000000 : ℝ)*base81 + (38119681/5000000000000000000000 : ℝ)*base90 + (38119681/5000000000000000000000 : ℝ)*base92 + (38119681/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1148_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1148_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1148_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1148_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1148_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1148_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1148_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
