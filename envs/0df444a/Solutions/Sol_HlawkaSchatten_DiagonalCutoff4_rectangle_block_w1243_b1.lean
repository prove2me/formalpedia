-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1243_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:20:08.462527+00:00
-- url     : https://prove2.me/submissions/00bf9314-69a0-430a-b9c7-2f4c69208948

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
theorem support_rectangle_w1243_s3_0 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116667897/10000000000 : ℝ)*x 0 + (2709784341/5000000000 : ℝ)*x 1 + (5240696267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116667897/10000000000 : ℝ)^2109 ≤ (514655024719/4000000000000 : ℝ)^1597 := by
    have hnat : (2116667897 : ℕ)^2109*4000000000000^1597 ≤ 514655024719^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116667897 10000000000 514655024719 4000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709784341/5000000000 : ℝ)^2109 ≤ (44532134825251/100000000000000 : ℝ)^1597 := by
    have hnat : (2709784341 : ℕ)^2109*100000000000000^1597 ≤ 44532134825251^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709784341 5000000000 44532134825251 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240696267/10000000000 : ℝ)^2109 ≤ (42601489531321/100000000000000 : ℝ)^1597 := by
    have hnat : (5240696267 : ℕ)^2109*100000000000000^1597 ≤ 42601489531321^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240696267 10000000000 42601489531321 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116667897/10000000000 : ℝ), (2709784341/5000000000 : ℝ), (5240696267/10000000000 : ℝ)] ![(514655024719/4000000000000 : ℝ), (44532134825251/100000000000000 : ℝ), (42601489531321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116667897/10000000000 : ℝ)|^2109 ≤ (514655024719/4000000000000 : ℝ)^1597
        have hw : |(-2116667897/10000000000 : ℝ)|=(2116667897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709784341/5000000000 : ℝ)|^2109 ≤ (44532134825251/100000000000000 : ℝ)^1597
        have hw : |(2709784341/5000000000 : ℝ)|=(2709784341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240696267/10000000000 : ℝ)|^2109 ≤ (42601489531321/100000000000000 : ℝ)^1597
        have hw : |(5240696267/10000000000 : ℝ)|=(5240696267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s3_1 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668933339/1250000000 : ℝ)*x 0 + (-1103957989/5000000000 : ℝ)*x 1 + (1310174097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668933339/1250000000 : ℝ)^2109 ≤ (21897317494493/50000000000000 : ℝ)^1597 := by
    have hnat : (668933339 : ℕ)^2109*50000000000000^1597 ≤ 21897317494493^1597*1250000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668933339 1250000000 21897317494493 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103957989/5000000000 : ℝ)^2109 ≤ (2720774832561/20000000000000 : ℝ)^1597 := by
    have hnat : (1103957989 : ℕ)^2109*20000000000000^1597 ≤ 2720774832561^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103957989 5000000000 2720774832561 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310174097/2500000000 : ℝ)^2109 ≤ (665648294223/1562500000000 : ℝ)^1597 := by
    have hnat : (1310174097 : ℕ)^2109*1562500000000^1597 ≤ 665648294223^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310174097 2500000000 665648294223 1562500000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668933339/1250000000 : ℝ), (-1103957989/5000000000 : ℝ), (1310174097/2500000000 : ℝ)] ![(21897317494493/50000000000000 : ℝ), (2720774832561/20000000000000 : ℝ), (665648294223/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668933339/1250000000 : ℝ)|^2109 ≤ (21897317494493/50000000000000 : ℝ)^1597
        have hw : |(668933339/1250000000 : ℝ)|=(668933339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103957989/5000000000 : ℝ)|^2109 ≤ (2720774832561/20000000000000 : ℝ)^1597
        have hw : |(-1103957989/5000000000 : ℝ)|=(1103957989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310174097/2500000000 : ℝ)|^2109 ≤ (665648294223/1562500000000 : ℝ)^1597
        have hw : |(1310174097/2500000000 : ℝ)|=(1310174097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s3_2 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5351466637/10000000000 : ℝ)*x 0 + (5240696827/10000000000 : ℝ)*x 1 + (-4415831/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351466637/10000000000 : ℝ)^2109 ≤ (21897317089217/50000000000000 : ℝ)^1597 := by
    have hnat : (5351466637 : ℕ)^2109*50000000000000^1597 ≤ 21897317089217^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351466637 10000000000 21897317089217 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240696827/10000000000 : ℝ)^2109 ≤ (10650373885749/25000000000000 : ℝ)^1597 := by
    have hnat : (5240696827 : ℕ)^2109*25000000000000^1597 ≤ 10650373885749^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240696827 10000000000 10650373885749 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4415831/20000000 : ℝ)^2109 ≤ (1700483784179/12500000000000 : ℝ)^1597 := by
    have hnat : (4415831 : ℕ)^2109*12500000000000^1597 ≤ 1700483784179^1597*20000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415831 20000000 1700483784179 12500000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351466637/10000000000 : ℝ), (5240696827/10000000000 : ℝ), (-4415831/20000000 : ℝ)] ![(21897317089217/50000000000000 : ℝ), (10650373885749/25000000000000 : ℝ), (1700483784179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351466637/10000000000 : ℝ)|^2109 ≤ (21897317089217/50000000000000 : ℝ)^1597
        have hw : |(5351466637/10000000000 : ℝ)|=(5351466637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240696827/10000000000 : ℝ)|^2109 ≤ (10650373885749/25000000000000 : ℝ)^1597
        have hw : |(5240696827/10000000000 : ℝ)|=(5240696827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4415831/20000000 : ℝ)|^2109 ≤ (1700483784179/12500000000000 : ℝ)^1597
        have hw : |(-4415831/20000000 : ℝ)|=(4415831/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s3_3 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4348942361/10000000000 : ℝ)*x 0 + (4171156577/10000000000 : ℝ)*x 1 + (4427813/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348942361/10000000000 : ℝ)^2109 ≤ (33300368769167/100000000000000 : ℝ)^1597 := by
    have hnat : (4348942361 : ℕ)^2109*100000000000000^1597 ≤ 33300368769167^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348942361 10000000000 33300368769167 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171156577/10000000000 : ℝ)^2109 ≤ (15757245469611/50000000000000 : ℝ)^1597 := by
    have hnat : (4171156577 : ℕ)^2109*50000000000000^1597 ≤ 15757245469611^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171156577 10000000000 15757245469611 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4427813/9765625 : ℝ)^2109 ≤ (7037028056153/20000000000000 : ℝ)^1597 := by
    have hnat : (4427813 : ℕ)^2109*20000000000000^1597 ≤ 7037028056153^1597*9765625^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427813 9765625 7037028056153 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348942361/10000000000 : ℝ), (4171156577/10000000000 : ℝ), (4427813/9765625 : ℝ)] ![(33300368769167/100000000000000 : ℝ), (15757245469611/50000000000000 : ℝ), (7037028056153/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348942361/10000000000 : ℝ)|^2109 ≤ (33300368769167/100000000000000 : ℝ)^1597
        have hw : |(4348942361/10000000000 : ℝ)|=(4348942361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171156577/10000000000 : ℝ)|^2109 ≤ (15757245469611/50000000000000 : ℝ)^1597
        have hw : |(4171156577/10000000000 : ℝ)|=(4171156577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4427813/9765625 : ℝ)|^2109 ≤ (7037028056153/20000000000000 : ℝ)^1597
        have hw : |(4427813/9765625 : ℝ)|=(4427813/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s3_4 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058341109/5000000000 : ℝ)*x 0 + (655168243/1250000000 : ℝ)*x 1 + (270945767/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058341109/5000000000 : ℝ)^2109 ≤ (2573298115713/20000000000000 : ℝ)^1597 := by
    have hnat : (1058341109 : ℕ)^2109*20000000000000^1597 ≤ 2573298115713^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058341109 5000000000 2573298115713 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655168243/1250000000 : ℝ)^2109 ≤ (42608464039367/100000000000000 : ℝ)^1597 := by
    have hnat : (655168243 : ℕ)^2109*100000000000000^1597 ≤ 42608464039367^1597*1250000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655168243 1250000000 42608464039367 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270945767/500000000 : ℝ)^2109 ≤ (8905009074739/20000000000000 : ℝ)^1597 := by
    have hnat : (270945767 : ℕ)^2109*20000000000000^1597 ≤ 8905009074739^1597*500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270945767 500000000 8905009074739 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058341109/5000000000 : ℝ), (655168243/1250000000 : ℝ), (270945767/500000000 : ℝ)] ![(2573298115713/20000000000000 : ℝ), (42608464039367/100000000000000 : ℝ), (8905009074739/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058341109/5000000000 : ℝ)|^2109 ≤ (2573298115713/20000000000000 : ℝ)^1597
        have hw : |(-1058341109/5000000000 : ℝ)|=(1058341109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655168243/1250000000 : ℝ)|^2109 ≤ (42608464039367/100000000000000 : ℝ)^1597
        have hw : |(655168243/1250000000 : ℝ)|=(655168243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270945767/500000000 : ℝ)|^2109 ≤ (8905009074739/20000000000000 : ℝ)^1597
        have hw : |(270945767/500000000 : ℝ)|=(270945767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s3_5 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652914657/5000000000 : ℝ)*x 0 + (-507424233/2500000000 : ℝ)*x 1 + (2709457559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652914657/5000000000 : ℝ)^2109 ≤ (10825522653789/25000000000000 : ℝ)^1597 := by
    have hnat : (2652914657 : ℕ)^2109*25000000000000^1597 ≤ 10825522653789^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652914657 5000000000 10825522653789 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507424233/2500000000 : ℝ)^2109 ≤ (12172866408273/100000000000000 : ℝ)^1597 := by
    have hnat : (507424233 : ℕ)^2109*100000000000000^1597 ≤ 12172866408273^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507424233 2500000000 12172866408273 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709457559/5000000000 : ℝ)^2109 ≤ (44525042964807/100000000000000 : ℝ)^1597 := by
    have hnat : (2709457559 : ℕ)^2109*100000000000000^1597 ≤ 44525042964807^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709457559 5000000000 44525042964807 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652914657/5000000000 : ℝ), (-507424233/2500000000 : ℝ), (2709457559/5000000000 : ℝ)] ![(10825522653789/25000000000000 : ℝ), (12172866408273/100000000000000 : ℝ), (44525042964807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652914657/5000000000 : ℝ)|^2109 ≤ (10825522653789/25000000000000 : ℝ)^1597
        have hw : |(2652914657/5000000000 : ℝ)|=(2652914657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507424233/2500000000 : ℝ)|^2109 ≤ (12172866408273/100000000000000 : ℝ)^1597
        have hw : |(-507424233/2500000000 : ℝ)|=(507424233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709457559/5000000000 : ℝ)|^2109 ≤ (44525042964807/100000000000000 : ℝ)^1597
        have hw : |(2709457559/5000000000 : ℝ)|=(2709457559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s3_6 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305829139/10000000000 : ℝ)*x 0 + (54189153/100000000 : ℝ)*x 1 + (-2029696921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305829139/10000000000 : ℝ)^2109 ≤ (21651044364527/50000000000000 : ℝ)^1597 := by
    have hnat : (5305829139 : ℕ)^2109*50000000000000^1597 ≤ 21651044364527^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305829139 10000000000 21651044364527 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54189153/100000000 : ℝ)^2109 ≤ (44525044939661/100000000000000 : ℝ)^1597 := by
    have hnat : (54189153 : ℕ)^2109*100000000000000^1597 ≤ 44525044939661^1597*100000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54189153 100000000 44525044939661 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2029696921/10000000000 : ℝ)^2109 ≤ (12172866321151/100000000000000 : ℝ)^1597 := by
    have hnat : (2029696921 : ℕ)^2109*100000000000000^1597 ≤ 12172866321151^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029696921 10000000000 12172866321151 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305829139/10000000000 : ℝ), (54189153/100000000 : ℝ), (-2029696921/10000000000 : ℝ)] ![(21651044364527/50000000000000 : ℝ), (44525044939661/100000000000000 : ℝ), (12172866321151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305829139/10000000000 : ℝ)|^2109 ≤ (21651044364527/50000000000000 : ℝ)^1597
        have hw : |(5305829139/10000000000 : ℝ)|=(5305829139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54189153/100000000 : ℝ)|^2109 ≤ (44525044939661/100000000000000 : ℝ)^1597
        have hw : |(54189153/100000000 : ℝ)|=(54189153/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2029696921/10000000000 : ℝ)|^2109 ≤ (12172866321151/100000000000000 : ℝ)^1597
        have hw : |(-2029696921/10000000000 : ℝ)|=(2029696921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s3_7 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1087242727/2500000000 : ℝ)*x 0 + (2266381143/5000000000 : ℝ)*x 1 + (166899259/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087242727/2500000000 : ℝ)^2109 ≤ (33300657436731/100000000000000 : ℝ)^1597 := by
    have hnat : (1087242727 : ℕ)^2109*100000000000000^1597 ≤ 33300657436731^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087242727 2500000000 33300657436731 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266381143/5000000000 : ℝ)^2109 ≤ (17585815824649/50000000000000 : ℝ)^1597 := by
    have hnat : (2266381143 : ℕ)^2109*50000000000000^1597 ≤ 17585815824649^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266381143 5000000000 17585815824649 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166899259/400000000 : ℝ)^2109 ≤ (31527710895609/100000000000000 : ℝ)^1597 := by
    have hnat : (166899259 : ℕ)^2109*100000000000000^1597 ≤ 31527710895609^1597*400000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166899259 400000000 31527710895609 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087242727/2500000000 : ℝ), (2266381143/5000000000 : ℝ), (166899259/400000000 : ℝ)] ![(33300657436731/100000000000000 : ℝ), (17585815824649/50000000000000 : ℝ), (31527710895609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087242727/2500000000 : ℝ)|^2109 ≤ (33300657436731/100000000000000 : ℝ)^1597
        have hw : |(1087242727/2500000000 : ℝ)|=(1087242727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2266381143/5000000000 : ℝ)|^2109 ≤ (17585815824649/50000000000000 : ℝ)^1597
        have hw : |(2266381143/5000000000 : ℝ)|=(2266381143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166899259/400000000 : ℝ)|^2109 ≤ (31527710895609/100000000000000 : ℝ)^1597
        have hw : |(166899259/400000000 : ℝ)|=(166899259/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1243_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (811/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5457/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (147/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (811/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (811/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (811/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (811/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (811/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (811/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9503/100000 : ℝ) ^ (8435/2048 : ℝ) ≤ (6168274564481383/100000000000000000000 : ℝ) := by
    have hpowers : (9503/100000 : ℝ)^8435 ≤ (6168274564481383/100000000000000000000 : ℝ)^2048 := by
      have hnat : (9503 : ℕ)^8435*100000000000000000000^2048 ≤ 6168274564481383^2048*100000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9503 100000 6168274564481383 100000000000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9503/100000 : ℝ)) (X := (6168274564481383/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (811/5000 : ℝ) ^ (8435/2048 : ℝ) ≤ (13944857802459101/25000000000000000000 : ℝ) := by
    have hpowers : (811/5000 : ℝ)^8435 ≤ (13944857802459101/25000000000000000000 : ℝ)^2048 := by
      have hnat : (811 : ℕ)^8435*25000000000000000000^2048 ≤ 13944857802459101^2048*5000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        811 5000 13944857802459101 25000000000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (811/5000 : ℝ)) (X := (13944857802459101/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006168274564481383/50000000000000000000 : ℝ) ≤ (5000149757395701/5000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (50006168274564481383/50000000000000000000 : ℝ)^2048 ≤ (5000149757395701/5000000000000000 : ℝ)^8435 := by
      have hnat : (50006168274564481383 : ℕ)^2048*5000000000000000^8435 ≤ 5000149757395701^8435*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006168274564481383 50000000000000000000 5000149757395701 5000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000149757395701/5000000000000000 : ℝ)) (X := (50006168274564481383/50000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100061947705774317787/100000000000000000000 : ℝ) ≤ (1250187965555811/1250000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (100061947705774317787/100000000000000000000 : ℝ)^2048 ≤ (1250187965555811/1250000000000000 : ℝ)^8435 := by
      have hnat : (100061947705774317787 : ℕ)^2048*1250000000000000^8435 ≤ 1250187965555811^8435*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061947705774317787 100000000000000000000 1250187965555811 1250000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250187965555811/1250000000000000 : ℝ)) (X := (100061947705774317787/100000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12513944857802459101/12500000000000000000 : ℝ) ≤ (5001353967050787/5000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (12513944857802459101/12500000000000000000 : ℝ)^2048 ≤ (5001353967050787/5000000000000000 : ℝ)^8435 := by
      have hnat : (12513944857802459101 : ℕ)^2048*5000000000000000^8435 ≤ 5001353967050787^8435*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12513944857802459101 12500000000000000000 5001353967050787 5000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001353967050787/5000000000000000 : ℝ)) (X := (12513944857802459101/12500000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6168274564481383/100000000000000000000 : ℝ) ≤ ((11191520772024880453/11195000000000000000 : ℝ)+2*(200701609181/111950000000000 : ℝ)*(9503/100000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (11191520772024880453/11195000000000000000 : ℝ)+2*(200701609181/111950000000000 : ℝ)*(9503/100000 : ℝ)=(5000149757395701/5000000000000000 : ℝ) by norm_num, show 1+2*(6168274564481383/100000000000000000000 : ℝ)=(50006168274564481383/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13944857802459101/25000000000000000000 : ℝ)+(6168274564481383/100000000000000000000 : ℝ) ≤ ((11191520772024880453/11195000000000000000 : ℝ)+(200701609181/111950000000000 : ℝ)*((811/5000 : ℝ)+(9503/100000 : ℝ)))^(8435/2048 : ℝ) := by
    rw [show (11191520772024880453/11195000000000000000 : ℝ)+(200701609181/111950000000000 : ℝ)*((811/5000 : ℝ)+(9503/100000 : ℝ))=(1250187965555811/1250000000000000 : ℝ) by norm_num, show 1+(13944857802459101/25000000000000000000 : ℝ)+(6168274564481383/100000000000000000000 : ℝ)=(100061947705774317787/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13944857802459101/25000000000000000000 : ℝ) ≤ ((11191520772024880453/11195000000000000000 : ℝ)+2*(200701609181/111950000000000 : ℝ)*(811/5000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (11191520772024880453/11195000000000000000 : ℝ)+2*(200701609181/111950000000000 : ℝ)*(811/5000 : ℝ)=(5001353967050787/5000000000000000 : ℝ) by norm_num, show 1+2*(13944857802459101/25000000000000000000 : ℝ)=(12513944857802459101/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11191520772024880453/11195000000000000000 : ℝ)*(X 1 0+X 2 0)+(200701609181/111950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (9503/100000 : ℝ)) (hi := (811/5000 : ℝ)) (c := (11191520772024880453/11195000000000000000 : ℝ)) (alpha := (200701609181/111950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11191520772024880453/11195000000000000000 : ℝ)*(X 0 1+X 2 1)+(200701609181/111950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (9503/100000 : ℝ)) (hi := (811/5000 : ℝ)) (c := (11191520772024880453/11195000000000000000 : ℝ)) (alpha := (200701609181/111950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11191520772024880453/11195000000000000000 : ℝ)*(X 0 2+X 1 2)+(200701609181/111950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (9503/100000 : ℝ)) (hi := (811/5000 : ℝ)) (c := (11191520772024880453/11195000000000000000 : ℝ)) (alpha := (200701609181/111950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2116667897/10000000000 : ℝ)*X 0 0+(2709784341/5000000000 : ℝ)*X 0 1+(5240696267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668933339/1250000000 : ℝ)*X 1 0+(-1103957989/5000000000 : ℝ)*X 1 1+(1310174097/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351466637/10000000000 : ℝ)*X 2 0+(5240696827/10000000000 : ℝ)*X 2 1+(-4415831/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348942361/10000000000 : ℝ)*X 0 0+(4171156577/10000000000 : ℝ)*X 0 1+(4427813/9765625 : ℝ)*X 0 2+(4348942361/10000000000 : ℝ)*X 1 0+(4171156577/10000000000 : ℝ)*X 1 1+(4427813/9765625 : ℝ)*X 1 2+(4348942361/10000000000 : ℝ)*X 2 0+(4171156577/10000000000 : ℝ)*X 2 1+(4427813/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1058341109/5000000000 : ℝ)*X 0 0+(655168243/1250000000 : ℝ)*X 0 1+(270945767/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652914657/5000000000 : ℝ)*X 1 0+(-507424233/2500000000 : ℝ)*X 1 1+(2709457559/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305829139/10000000000 : ℝ)*X 2 0+(54189153/100000000 : ℝ)*X 2 1+(-2029696921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087242727/2500000000 : ℝ)*X 0 0+(2266381143/5000000000 : ℝ)*X 0 1+(166899259/400000000 : ℝ)*X 0 2+(1087242727/2500000000 : ℝ)*X 1 0+(2266381143/5000000000 : ℝ)*X 1 1+(166899259/400000000 : ℝ)*X 1 2+(1087242727/2500000000 : ℝ)*X 2 0+(2266381143/5000000000 : ℝ)*X 2 1+(166899259/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75642892002093362857215147/17492187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2410521/625000000000 : ℝ)*(base19) + (1867873/5000000000000 : ℝ)*(base23) + (43744609/25000000000000 : ℝ)*(lower2) + (53448853/100000000000000 : ℝ)*(lower3) + (65203340030071/1562500000000 : ℝ)*(major0) + (65203340030071/1562500000000 : ℝ)*(major1) + (65203340030071/1562500000000 : ℝ)*(major2) + (223623814347041/4000000000000 : ℝ)*(sp0) + (1397653016830271/25000000000000 : ℝ)*(sp1) + (2795309549669923/50000000000000 : ℝ)*(sp2) + (1377701508359897/50000000000000 : ℝ)*(sp3) + (23778021281/100000000000000 : ℝ)*(sp4) + (6683692861/100000000000000 : ℝ)*(sp5) + (1306571483/25000000000000 : ℝ)*(sp7) + (1377704121502863/50000000000000 : ℝ)*(f.failure) + (2795309568348653/50000000000000 : ℝ)*(f.sum) + (28398563295437/11195000000000000000000000000 : ℝ)*base66 + (7179280135545913/17492187500000000000000000000000 : ℝ)*base67 + (221551031274548799/34984375000000000000000000000000 : ℝ)*base70 + (10635490655295913/17492187500000000000000000000000 : ℝ)*base71 + (10936800485421/5597500000000000000000000000 : ℝ)*base74 + (2304350147658143/1093261718750000000000000000000 : ℝ)*base75 + (389684323273297837/17492187500000000000000000000000 : ℝ)*base78 + (197186674280920913/17492187500000000000000000000000 : ℝ)*base79 + (5718516569867/2798750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (246541/312500000000000000000 : ℝ)*base89 + (246541/312500000000000000000 : ℝ)*base91 + (246541/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (539177109244968208921439733/69968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4983447/250000000000 : ℝ)*(base19) + (235938193/12500000000000 : ℝ)*(base23) + (40321669/50000000000000 : ℝ)*(upper3) + (14606121/25000000000000 : ℝ)*(lower4) + (269799749/100000000000000 : ℝ)*(upper5) + (1050901773306413/25000000000000 : ℝ)*(major0) + (1050901773306413/25000000000000 : ℝ)*(major1) + (1050901773306413/25000000000000 : ℝ)*(major2) + (39699462259/100000000000000 : ℝ)*(sp1) + (36183413663/100000000000000 : ℝ)*(sp2) + (5631605149975577/100000000000000 : ℝ)*(sp4) + (2815781728567259/50000000000000 : ℝ)*(sp5) + (5631567079056369/100000000000000 : ℝ)*(sp6) + (693902194902511/25000000000000 : ℝ)*(sp7) + (693902194902511/25000000000000 : ℝ)*(f.failure) + (5631605149975577/100000000000000 : ℝ)*(f.sum) + (850977006827/5597500000000000000000000000 : ℝ)*base65 + (1803335275762545089/279875000000000000000000000000000 : ℝ)*base67 + (625124271498545089/279875000000000000000000000000000 : ℝ)*base69 + (369515292655045089/279875000000000000000000000000000 : ℝ)*base71 + (4240606053823/5597500000000000000000000000 : ℝ)*base74 + (3853662859026954911/279875000000000000000000000000000 : ℝ)*base76 + (875049429615295089/279875000000000000000000000000000 : ℝ)*base77 + (4870462083536670089/279875000000000000000000000000000 : ℝ)*base79 + (33554553356421/11195000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (938077/156250000000000000000 : ℝ)*base89 + (938077/156250000000000000000 : ℝ)*base91 + (938077/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1243_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (811/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5457/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (147/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1243_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1243_s4_0 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-105947499/500000000 : ℝ)*x 0 + (2698726953/5000000000 : ℝ)*x 1 + (5261315887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105947499/500000000 : ℝ)^2109 ≤ (2576939597483/20000000000000 : ℝ)^1597 := by
    have hnat : (105947499 : ℕ)^2109*20000000000000^1597 ≤ 2576939597483^1597*500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105947499 500000000 2576939597483 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698726953/5000000000 : ℝ)^2109 ≤ (22146159299299/50000000000000 : ℝ)^1597 := by
    have hnat : (2698726953 : ℕ)^2109*50000000000000^1597 ≤ 22146159299299^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698726953 5000000000 22146159299299 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261315887/10000000000 : ℝ)^2109 ≤ (21411491697033/50000000000000 : ℝ)^1597 := by
    have hnat : (5261315887 : ℕ)^2109*50000000000000^1597 ≤ 21411491697033^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261315887 10000000000 21411491697033 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105947499/500000000 : ℝ), (2698726953/5000000000 : ℝ), (5261315887/10000000000 : ℝ)] ![(2576939597483/20000000000000 : ℝ), (22146159299299/50000000000000 : ℝ), (21411491697033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105947499/500000000 : ℝ)|^2109 ≤ (2576939597483/20000000000000 : ℝ)^1597
        have hw : |(-105947499/500000000 : ℝ)|=(105947499/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698726953/5000000000 : ℝ)|^2109 ≤ (22146159299299/50000000000000 : ℝ)^1597
        have hw : |(2698726953/5000000000 : ℝ)|=(2698726953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261315887/10000000000 : ℝ)|^2109 ≤ (21411491697033/50000000000000 : ℝ)^1597
        have hw : |(5261315887/10000000000 : ℝ)|=(5261315887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s4_1 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336473061/2500000000 : ℝ)*x 0 + (-2188068953/10000000000 : ℝ)*x 1 + (1315328973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336473061/2500000000 : ℝ)^2109 ≤ (4373439975091/10000000000000 : ℝ)^1597 := by
    have hnat : (1336473061 : ℕ)^2109*10000000000000^1597 ≤ 4373439975091^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336473061 2500000000 4373439975091 10000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188068953/10000000000 : ℝ)^2109 ≤ (1680327097039/12500000000000 : ℝ)^1597 := by
    have hnat : (2188068953 : ℕ)^2109*12500000000000^1597 ≤ 1680327097039^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188068953 10000000000 1680327097039 12500000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315328973/2500000000 : ℝ)^2109 ≤ (42822983447809/100000000000000 : ℝ)^1597 := by
    have hnat : (1315328973 : ℕ)^2109*100000000000000^1597 ≤ 42822983447809^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315328973 2500000000 42822983447809 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336473061/2500000000 : ℝ), (-2188068953/10000000000 : ℝ), (1315328973/2500000000 : ℝ)] ![(4373439975091/10000000000000 : ℝ), (1680327097039/12500000000000 : ℝ), (42822983447809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336473061/2500000000 : ℝ)|^2109 ≤ (4373439975091/10000000000000 : ℝ)^1597
        have hw : |(1336473061/2500000000 : ℝ)|=(1336473061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2188068953/10000000000 : ℝ)|^2109 ≤ (1680327097039/12500000000000 : ℝ)^1597
        have hw : |(-2188068953/10000000000 : ℝ)|=(2188068953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315328973/2500000000 : ℝ)|^2109 ≤ (42822983447809/100000000000000 : ℝ)^1597
        have hw : |(1315328973/2500000000 : ℝ)|=(1315328973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s4_2 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345892313/10000000000 : ℝ)*x 0 + (526131577/1000000000 : ℝ)*x 1 + (-2188069023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345892313/10000000000 : ℝ)^2109 ≤ (43734400496369/100000000000000 : ℝ)^1597 := by
    have hnat : (5345892313 : ℕ)^2109*100000000000000^1597 ≤ 43734400496369^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345892313 10000000000 43734400496369 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526131577/1000000000 : ℝ)^2109 ≤ (42822982136473/100000000000000 : ℝ)^1597 := by
    have hnat : (526131577 : ℕ)^2109*100000000000000^1597 ≤ 42822982136473^1597*1000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526131577 1000000000 42822982136473 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188069023/10000000000 : ℝ)^2109 ≤ (13442617344239/100000000000000 : ℝ)^1597 := by
    have hnat : (2188069023 : ℕ)^2109*100000000000000^1597 ≤ 13442617344239^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188069023 10000000000 13442617344239 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345892313/10000000000 : ℝ), (526131577/1000000000 : ℝ), (-2188069023/10000000000 : ℝ)] ![(43734400496369/100000000000000 : ℝ), (42822982136473/100000000000000 : ℝ), (13442617344239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345892313/10000000000 : ℝ)|^2109 ≤ (43734400496369/100000000000000 : ℝ)^1597
        have hw : |(5345892313/10000000000 : ℝ)|=(5345892313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526131577/1000000000 : ℝ)|^2109 ≤ (42822982136473/100000000000000 : ℝ)^1597
        have hw : |(526131577/1000000000 : ℝ)|=(526131577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188069023/10000000000 : ℝ)|^2109 ≤ (13442617344239/100000000000000 : ℝ)^1597
        have hw : |(-2188069023/10000000000 : ℝ)|=(2188069023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s4_3 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4350313177/10000000000 : ℝ)*x 0 + (2107167049/5000000000 : ℝ)*x 1 + (4490553163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350313177/10000000000 : ℝ)^2109 ≤ (16657115580357/50000000000000 : ℝ)^1597 := by
    have hnat : (4350313177 : ℕ)^2109*50000000000000^1597 ≤ 16657115580357^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350313177 10000000000 16657115580357 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107167049/5000000000 : ℝ)^2109 ≤ (31946011544583/100000000000000 : ℝ)^1597 := by
    have hnat : (2107167049 : ℕ)^2109*100000000000000^1597 ≤ 31946011544583^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107167049 5000000000 31946011544583 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490553163/10000000000 : ℝ)^2109 ≤ (34739757284789/100000000000000 : ℝ)^1597 := by
    have hnat : (4490553163 : ℕ)^2109*100000000000000^1597 ≤ 34739757284789^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490553163 10000000000 34739757284789 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350313177/10000000000 : ℝ), (2107167049/5000000000 : ℝ), (4490553163/10000000000 : ℝ)] ![(16657115580357/50000000000000 : ℝ), (31946011544583/100000000000000 : ℝ), (34739757284789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350313177/10000000000 : ℝ)|^2109 ≤ (16657115580357/50000000000000 : ℝ)^1597
        have hw : |(4350313177/10000000000 : ℝ)|=(4350313177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2107167049/5000000000 : ℝ)|^2109 ≤ (31946011544583/100000000000000 : ℝ)^1597
        have hw : |(2107167049/5000000000 : ℝ)|=(2107167049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490553163/10000000000 : ℝ)|^2109 ≤ (34739757284789/100000000000000 : ℝ)^1597
        have hw : |(4490553163/10000000000 : ℝ)|=(4490553163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s4_4 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-529739037/2500000000 : ℝ)*x 0 + (2630846369/5000000000 : ℝ)*x 1 + (5397075551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529739037/2500000000 : ℝ)^2109 ≤ (12884747517579/100000000000000 : ℝ)^1597 := by
    have hnat : (529739037 : ℕ)^2109*100000000000000^1597 ≤ 12884747517579^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529739037 2500000000 12884747517579 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630846369/5000000000 : ℝ)^2109 ≤ (21413517041367/50000000000000 : ℝ)^1597 := by
    have hnat : (2630846369 : ℕ)^2109*50000000000000^1597 ≤ 21413517041367^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630846369 5000000000 21413517041367 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397075551/10000000000 : ℝ)^2109 ≤ (44288218392059/100000000000000 : ℝ)^1597 := by
    have hnat : (5397075551 : ℕ)^2109*100000000000000^1597 ≤ 44288218392059^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397075551 10000000000 44288218392059 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529739037/2500000000 : ℝ), (2630846369/5000000000 : ℝ), (5397075551/10000000000 : ℝ)] ![(12884747517579/100000000000000 : ℝ), (21413517041367/50000000000000 : ℝ), (44288218392059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529739037/2500000000 : ℝ)|^2109 ≤ (12884747517579/100000000000000 : ℝ)^1597
        have hw : |(-529739037/2500000000 : ℝ)|=(529739037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630846369/5000000000 : ℝ)|^2109 ≤ (21413517041367/50000000000000 : ℝ)^1597
        have hw : |(2630846369/5000000000 : ℝ)|=(2630846369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397075551/10000000000 : ℝ)|^2109 ≤ (44288218392059/100000000000000 : ℝ)^1597
        have hw : |(5397075551/10000000000 : ℝ)|=(5397075551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s4_5 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1327788829/2500000000 : ℝ)*x 0 + (-2052309361/10000000000 : ℝ)*x 1 + (5397075579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327788829/2500000000 : ℝ)^2109 ≤ (2167975102753/5000000000000 : ℝ)^1597 := by
    have hnat : (1327788829 : ℕ)^2109*5000000000000^1597 ≤ 2167975102753^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327788829 2500000000 2167975102753 5000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2052309361/10000000000 : ℝ)^2109 ≤ (6176139619847/50000000000000 : ℝ)^1597 := by
    have hnat : (2052309361 : ℕ)^2109*50000000000000^1597 ≤ 6176139619847^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052309361 10000000000 6176139619847 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397075579/10000000000 : ℝ)^2109 ≤ (44288218695489/100000000000000 : ℝ)^1597 := by
    have hnat : (5397075579 : ℕ)^2109*100000000000000^1597 ≤ 44288218695489^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397075579 10000000000 44288218695489 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327788829/2500000000 : ℝ), (-2052309361/10000000000 : ℝ), (5397075579/10000000000 : ℝ)] ![(2167975102753/5000000000000 : ℝ), (6176139619847/50000000000000 : ℝ), (44288218695489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327788829/2500000000 : ℝ)|^2109 ≤ (2167975102753/5000000000000 : ℝ)^1597
        have hw : |(1327788829/2500000000 : ℝ)|=(1327788829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2052309361/10000000000 : ℝ)|^2109 ≤ (6176139619847/50000000000000 : ℝ)^1597
        have hw : |(-2052309361/10000000000 : ℝ)|=(2052309361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397075579/10000000000 : ℝ)|^2109 ≤ (44288218695489/100000000000000 : ℝ)^1597
        have hw : |(5397075579/10000000000 : ℝ)|=(5397075579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s4_6 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655577613/5000000000 : ℝ)*x 0 + (5397075743/10000000000 : ℝ)*x 1 + (-2052309259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655577613/5000000000 : ℝ)^2109 ≤ (43359501084753/100000000000000 : ℝ)^1597 := by
    have hnat : (2655577613 : ℕ)^2109*100000000000000^1597 ≤ 43359501084753^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655577613 5000000000 43359501084753 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397075743/10000000000 : ℝ)^2109 ≤ (22144110236363/50000000000000 : ℝ)^1597 := by
    have hnat : (5397075743 : ℕ)^2109*50000000000000^1597 ≤ 22144110236363^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397075743 10000000000 22144110236363 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2052309259/10000000000 : ℝ)^2109 ≤ (2470455685793/20000000000000 : ℝ)^1597 := by
    have hnat : (2052309259 : ℕ)^2109*20000000000000^1597 ≤ 2470455685793^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052309259 10000000000 2470455685793 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655577613/5000000000 : ℝ), (5397075743/10000000000 : ℝ), (-2052309259/10000000000 : ℝ)] ![(43359501084753/100000000000000 : ℝ), (22144110236363/50000000000000 : ℝ), (2470455685793/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655577613/5000000000 : ℝ)|^2109 ≤ (43359501084753/100000000000000 : ℝ)^1597
        have hw : |(2655577613/5000000000 : ℝ)|=(2655577613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397075743/10000000000 : ℝ)|^2109 ≤ (22144110236363/50000000000000 : ℝ)^1597
        have hw : |(5397075743/10000000000 : ℝ)|=(5397075743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2052309259/10000000000 : ℝ)|^2109 ≤ (2470455685793/20000000000000 : ℝ)^1597
        have hw : |(-2052309259/10000000000 : ℝ)|=(2052309259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s4_7 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4350325703/10000000000 : ℝ)*x 0 + (561223577/1250000000 : ℝ)*x 1 + (4215101667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350325703/10000000000 : ℝ)^2109 ≤ (33314357836481/100000000000000 : ℝ)^1597 := by
    have hnat : (4350325703 : ℕ)^2109*100000000000000^1597 ≤ 33314357836481^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350325703 10000000000 33314357836481 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561223577/1250000000 : ℝ)^2109 ≤ (6946389313437/20000000000000 : ℝ)^1597 := by
    have hnat : (561223577 : ℕ)^2109*20000000000000^1597 ≤ 6946389313437^1597*1250000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561223577 1250000000 6946389313437 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4215101667/10000000000 : ℝ)^2109 ≤ (31953695581651/100000000000000 : ℝ)^1597 := by
    have hnat : (4215101667 : ℕ)^2109*100000000000000^1597 ≤ 31953695581651^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215101667 10000000000 31953695581651 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350325703/10000000000 : ℝ), (561223577/1250000000 : ℝ), (4215101667/10000000000 : ℝ)] ![(33314357836481/100000000000000 : ℝ), (6946389313437/20000000000000 : ℝ), (31953695581651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350325703/10000000000 : ℝ)|^2109 ≤ (33314357836481/100000000000000 : ℝ)^1597
        have hw : |(4350325703/10000000000 : ℝ)|=(4350325703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561223577/1250000000 : ℝ)|^2109 ≤ (6946389313437/20000000000000 : ℝ)^1597
        have hw : |(561223577/1250000000 : ℝ)|=(561223577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4215101667/10000000000 : ℝ)|^2109 ≤ (31953695581651/100000000000000 : ℝ)^1597
        have hw : |(4215101667/10000000000 : ℝ)|=(4215101667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1243_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5457/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11353/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (147/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5457/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (147/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5457/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (147/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5457/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (147/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5457/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (147/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5457/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (147/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5457/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5457/50000 : ℝ) ^ (8435/2048 : ℝ) ≤ (42613810802073/390625000000000000 : ℝ) := by
    have hpowers : (5457/50000 : ℝ)^8435 ≤ (42613810802073/390625000000000000 : ℝ)^2048 := by
      have hnat : (5457 : ℕ)^8435*390625000000000000^2048 ≤ 42613810802073^2048*50000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5457 50000 42613810802073 390625000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5457/50000 : ℝ)) (X := (42613810802073/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (147/1000 : ℝ) ^ (8435/2048 : ℝ) ≤ (1162303674657219/3125000000000000000 : ℝ) := by
    have hpowers : (147/1000 : ℝ)^8435 ≤ (1162303674657219/3125000000000000000 : ℝ)^2048 := by
      have hnat : (147 : ℕ)^8435*3125000000000000000^2048 ≤ 1162303674657219^2048*1000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        147 1000 1162303674657219 3125000000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (147/1000 : ℝ)) (X := (1162303674657219/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (195355113810802073/195312500000000000 : ℝ) ≤ (5000264849606851/5000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (195355113810802073/195312500000000000 : ℝ)^2048 ≤ (5000264849606851/5000000000000000 : ℝ)^8435 := by
      have hnat : (195355113810802073 : ℕ)^2048*5000000000000000^8435 ≤ 5000264849606851^8435*195312500000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195355113810802073 195312500000000000 5000264849606851 5000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000264849606851/5000000000000000 : ℝ)) (X := (195355113810802073/195312500000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126503214161073803/3125000000000000000 : ℝ) ≤ (5000583857184541/5000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (3126503214161073803/3125000000000000000 : ℝ)^2048 ≤ (5000583857184541/5000000000000000 : ℝ)^8435 := by
      have hnat : (3126503214161073803 : ℕ)^2048*5000000000000000^8435 ≤ 5000583857184541^8435*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126503214161073803 3125000000000000000 5000583857184541 5000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000583857184541/5000000000000000 : ℝ)) (X := (3126503214161073803/3125000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563662303674657219/1562500000000000000 : ℝ) ≤ (5000902864762231/5000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (1563662303674657219/1562500000000000000 : ℝ)^2048 ≤ (5000902864762231/5000000000000000 : ℝ)^8435 := by
      have hnat : (1563662303674657219 : ℕ)^2048*5000000000000000^8435 ≤ 5000902864762231^8435*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563662303674657219 1562500000000000000 5000902864762231 5000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000902864762231/5000000000000000 : ℝ)) (X := (1563662303674657219/1562500000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(42613810802073/390625000000000000 : ℝ) ≤ ((3154006570534286761/3155000000000000000 : ℝ)+2*(10633585923/6310000000000 : ℝ)*(5457/50000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (3154006570534286761/3155000000000000000 : ℝ)+2*(10633585923/6310000000000 : ℝ)*(5457/50000 : ℝ)=(5000264849606851/5000000000000000 : ℝ) by norm_num, show 1+2*(42613810802073/390625000000000000 : ℝ)=(195355113810802073/195312500000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1162303674657219/3125000000000000000 : ℝ)+(42613810802073/390625000000000000 : ℝ) ≤ ((3154006570534286761/3155000000000000000 : ℝ)+(10633585923/6310000000000 : ℝ)*((147/1000 : ℝ)+(5457/50000 : ℝ)))^(8435/2048 : ℝ) := by
    rw [show (3154006570534286761/3155000000000000000 : ℝ)+(10633585923/6310000000000 : ℝ)*((147/1000 : ℝ)+(5457/50000 : ℝ))=(5000583857184541/5000000000000000 : ℝ) by norm_num, show 1+(1162303674657219/3125000000000000000 : ℝ)+(42613810802073/390625000000000000 : ℝ)=(3126503214161073803/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1162303674657219/3125000000000000000 : ℝ) ≤ ((3154006570534286761/3155000000000000000 : ℝ)+2*(10633585923/6310000000000 : ℝ)*(147/1000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (3154006570534286761/3155000000000000000 : ℝ)+2*(10633585923/6310000000000 : ℝ)*(147/1000 : ℝ)=(5000902864762231/5000000000000000 : ℝ) by norm_num, show 1+2*(1162303674657219/3125000000000000000 : ℝ)=(1563662303674657219/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3154006570534286761/3155000000000000000 : ℝ)*(X 1 0+X 2 0)+(10633585923/6310000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (5457/50000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (3154006570534286761/3155000000000000000 : ℝ)) (alpha := (10633585923/6310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3154006570534286761/3155000000000000000 : ℝ)*(X 0 1+X 2 1)+(10633585923/6310000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (5457/50000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (3154006570534286761/3155000000000000000 : ℝ)) (alpha := (10633585923/6310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3154006570534286761/3155000000000000000 : ℝ)*(X 0 2+X 1 2)+(10633585923/6310000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (5457/50000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (3154006570534286761/3155000000000000000 : ℝ)) (alpha := (10633585923/6310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-105947499/500000000 : ℝ)*X 0 0+(2698726953/5000000000 : ℝ)*X 0 1+(5261315887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336473061/2500000000 : ℝ)*X 1 0+(-2188068953/10000000000 : ℝ)*X 1 1+(1315328973/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345892313/10000000000 : ℝ)*X 2 0+(526131577/1000000000 : ℝ)*X 2 1+(-2188069023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350313177/10000000000 : ℝ)*X 0 0+(2107167049/5000000000 : ℝ)*X 0 1+(4490553163/10000000000 : ℝ)*X 0 2+(4350313177/10000000000 : ℝ)*X 1 0+(2107167049/5000000000 : ℝ)*X 1 1+(4490553163/10000000000 : ℝ)*X 1 2+(4350313177/10000000000 : ℝ)*X 2 0+(2107167049/5000000000 : ℝ)*X 2 1+(4490553163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-529739037/2500000000 : ℝ)*X 0 0+(2630846369/5000000000 : ℝ)*X 0 1+(5397075551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327788829/2500000000 : ℝ)*X 1 0+(-2052309361/10000000000 : ℝ)*X 1 1+(5397075579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655577613/5000000000 : ℝ)*X 2 0+(5397075743/10000000000 : ℝ)*X 2 1+(-2052309259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350325703/10000000000 : ℝ)*X 0 0+(561223577/1250000000 : ℝ)*X 0 1+(4215101667/10000000000 : ℝ)*X 0 2+(4350325703/10000000000 : ℝ)*X 1 0+(561223577/1250000000 : ℝ)*X 1 1+(4215101667/10000000000 : ℝ)*X 1 2+(4350325703/10000000000 : ℝ)*X 2 0+(561223577/1250000000 : ℝ)*X 2 1+(4215101667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (788894386135482854154078759/78875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (422688629/20000000000000 : ℝ)*(base19) + (1079673091/50000000000000 : ℝ)*(base23) + (79590927/25000000000000 : ℝ)*(upper3) + (13072649/50000000000000 : ℝ)*(upper4) + (97402219/50000000000000 : ℝ)*(upper5) + (2741490237385773/50000000000000 : ℝ)*(major0) + (2741490237385773/50000000000000 : ℝ)*(major1) + (2741490237385773/50000000000000 : ℝ)*(major2) + (7345541041818537/100000000000000 : ℝ)*(sp0) + (1836397379499773/25000000000000 : ℝ)*(sp1) + (3672794736048027/50000000000000 : ℝ)*(sp2) + (3620340381368201/100000000000000 : ℝ)*(sp3) + (505896237/1000000000000 : ℝ)*(sp4) + (1787708643/6250000000000 : ℝ)*(sp7) + (362036898470649/10000000000000 : ℝ)*(f.failure) + (7345591631442237/100000000000000 : ℝ)*(f.sum) + (620773989141/126200000000000000000000000 : ℝ)*base65 + (5274511744213848747/157750000000000000000000000000000 : ℝ)*base68 + (1256328771251348747/157750000000000000000000000000000 : ℝ)*base70 + (983706777113401253/157750000000000000000000000000000 : ℝ)*base71 + (596917306707/315500000000000000000000000 : ℝ)*base74 + (2381372436850098747/157750000000000000000000000000000 : ℝ)*base76 + (1180201682994901253/157750000000000000000000000000000 : ℝ)*base77 + (786275860213348747/157750000000000000000000000000000 : ℝ)*base80 + (4103533944589/631000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1154043/62500000000000000000 : ℝ)*base89 + (1154043/62500000000000000000 : ℝ)*base91 + (1154043/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121014740274162859580295963/15775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (320002141/25000000000000 : ℝ)*(base19) + (162319847/12500000000000 : ℝ)*(base23) + (1560529/4000000000000 : ℝ)*(upper2) + (33456577/12500000000000 : ℝ)*(upper3) + (32758089/20000000000000 : ℝ)*(upper5) + (551348248772013/10000000000000 : ℝ)*(major0) + (551348248772013/10000000000000 : ℝ)*(major1) + (551348248772013/10000000000000 : ℝ)*(major2) + (12603436839/50000000000000 : ℝ)*(sp1) + (2246843997/6250000000000 : ℝ)*(sp2) + (7386455495211119/100000000000000 : ℝ)*(sp4) + (3693214504164439/50000000000000 : ℝ)*(sp5) + (7386418247148391/100000000000000 : ℝ)*(sp6) + (1820254612259587/50000000000000 : ℝ)*(sp7) + (1820254612259587/50000000000000 : ℝ)*(f.failure) + (7386455495211119/100000000000000 : ℝ)*(f.sum) + (102168052297/63100000000000000000000000 : ℝ)*base65 + (122774588013419893/31550000000000000000000000000000 : ℝ)*base67 + (11054851070869893/31550000000000000000000000000000 : ℝ)*base69 + (59850599279619893/31550000000000000000000000000000 : ℝ)*base71 + (68482732183/39437500000000000000000000 : ℝ)*base73 + (111576004168919893/31550000000000000000000000000000 : ℝ)*base75 + (52181000553519893/31550000000000000000000000000000 : ℝ)*base77 + (195233935550369893/31550000000000000000000000000000 : ℝ)*base79 + (1329727035497/631000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (315609/312500000000000000000 : ℝ)*base89 + (315609/312500000000000000000 : ℝ)*base91 + (315609/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1243_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5457/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1243_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1243_s5_0 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059699841/5000000000 : ℝ)*x 0 + (5392387701/10000000000 : ℝ)*x 1 + (1053217263/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059699841/5000000000 : ℝ)^2109 ≤ (12888309297619/100000000000000 : ℝ)^1597 := by
    have hnat : (1059699841 : ℕ)^2109*100000000000000^1597 ≤ 12888309297619^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059699841 5000000000 12888309297619 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392387701/10000000000 : ℝ)^2109 ≤ (2764839008547/6250000000000 : ℝ)^1597 := by
    have hnat : (5392387701 : ℕ)^2109*6250000000000^1597 ≤ 2764839008547^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392387701 10000000000 2764839008547 6250000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053217263/2000000000 : ℝ)^2109 ≤ (5359283317469/12500000000000 : ℝ)^1597 := by
    have hnat : (1053217263 : ℕ)^2109*12500000000000^1597 ≤ 5359283317469^1597*2000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053217263 2000000000 5359283317469 12500000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059699841/5000000000 : ℝ), (5392387701/10000000000 : ℝ), (1053217263/2000000000 : ℝ)] ![(12888309297619/100000000000000 : ℝ), (2764839008547/6250000000000 : ℝ), (5359283317469/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059699841/5000000000 : ℝ)|^2109 ≤ (12888309297619/100000000000000 : ℝ)^1597
        have hw : |(-1059699841/5000000000 : ℝ)|=(1059699841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392387701/10000000000 : ℝ)|^2109 ≤ (2764839008547/6250000000000 : ℝ)^1597
        have hw : |(5392387701/10000000000 : ℝ)|=(5392387701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053217263/2000000000 : ℝ)|^2109 ≤ (5359283317469/12500000000000 : ℝ)^1597
        have hw : |(1053217263/2000000000 : ℝ)|=(1053217263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s5_1 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672304761/5000000000 : ℝ)*x 0 + (-436690901/2000000000 : ℝ)*x 1 + (2633043161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672304761/5000000000 : ℝ)^2109 ≤ (2186027103637/5000000000000 : ℝ)^1597 := by
    have hnat : (2672304761 : ℕ)^2109*5000000000000^1597 ≤ 2186027103637^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672304761 5000000000 2186027103637 5000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436690901/2000000000 : ℝ)^2109 ≤ (3351297825323/25000000000000 : ℝ)^1597 := by
    have hnat : (436690901 : ℕ)^2109*25000000000000^1597 ≤ 3351297825323^1597*2000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436690901 2000000000 3351297825323 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633043161/5000000000 : ℝ)^2109 ≤ (21437133307507/50000000000000 : ℝ)^1597 := by
    have hnat : (2633043161 : ℕ)^2109*50000000000000^1597 ≤ 21437133307507^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633043161 5000000000 21437133307507 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672304761/5000000000 : ℝ), (-436690901/2000000000 : ℝ), (2633043161/5000000000 : ℝ)] ![(2186027103637/5000000000000 : ℝ), (3351297825323/25000000000000 : ℝ), (21437133307507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672304761/5000000000 : ℝ)|^2109 ≤ (2186027103637/5000000000000 : ℝ)^1597
        have hw : |(2672304761/5000000000 : ℝ)|=(2672304761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436690901/2000000000 : ℝ)|^2109 ≤ (3351297825323/25000000000000 : ℝ)^1597
        have hw : |(-436690901/2000000000 : ℝ)|=(436690901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633043161/5000000000 : ℝ)|^2109 ≤ (21437133307507/50000000000000 : ℝ)^1597
        have hw : |(2633043161/5000000000 : ℝ)|=(2633043161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s5_2 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672304981/5000000000 : ℝ)*x 0 + (5266086239/10000000000 : ℝ)*x 1 + (-545863507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672304981/5000000000 : ℝ)^2109 ≤ (21860273413013/50000000000000 : ℝ)^1597 := by
    have hnat : (2672304981 : ℕ)^2109*50000000000000^1597 ≤ 21860273413013^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672304981 5000000000 21860273413013 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266086239/10000000000 : ℝ)^2109 ≤ (42874265722617/100000000000000 : ℝ)^1597 := by
    have hnat : (5266086239 : ℕ)^2109*100000000000000^1597 ≤ 42874265722617^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266086239 10000000000 42874265722617 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545863507/2500000000 : ℝ)^2109 ≤ (6702593716947/50000000000000 : ℝ)^1597 := by
    have hnat : (545863507 : ℕ)^2109*50000000000000^1597 ≤ 6702593716947^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545863507 2500000000 6702593716947 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672304981/5000000000 : ℝ), (5266086239/10000000000 : ℝ), (-545863507/2500000000 : ℝ)] ![(21860273413013/50000000000000 : ℝ), (42874265722617/100000000000000 : ℝ), (6702593716947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672304981/5000000000 : ℝ)|^2109 ≤ (21860273413013/50000000000000 : ℝ)^1597
        have hw : |(2672304981/5000000000 : ℝ)|=(2672304981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266086239/10000000000 : ℝ)|^2109 ≤ (42874265722617/100000000000000 : ℝ)^1597
        have hw : |(5266086239/10000000000 : ℝ)|=(5266086239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-545863507/2500000000 : ℝ)|^2109 ≤ (6702593716947/50000000000000 : ℝ)^1597
        have hw : |(-545863507/2500000000 : ℝ)|=(545863507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s5_3 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4350575873/10000000000 : ℝ)*x 0 + (4224280447/10000000000 : ℝ)*x 1 + (44805399/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350575873/10000000000 : ℝ)^2109 ≤ (33316887836757/100000000000000 : ℝ)^1597 := by
    have hnat : (4350575873 : ℕ)^2109*100000000000000^1597 ≤ 33316887836757^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350575873 10000000000 33316887836757 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224280447/10000000000 : ℝ)^2109 ≤ (32045617940713/100000000000000 : ℝ)^1597 := by
    have hnat : (4224280447 : ℕ)^2109*100000000000000^1597 ≤ 32045617940713^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224280447 10000000000 32045617940713 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44805399/100000000 : ℝ)^2109 ≤ (3463749420191/10000000000000 : ℝ)^1597 := by
    have hnat : (44805399 : ℕ)^2109*10000000000000^1597 ≤ 3463749420191^1597*100000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44805399 100000000 3463749420191 10000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350575873/10000000000 : ℝ), (4224280447/10000000000 : ℝ), (44805399/100000000 : ℝ)] ![(33316887836757/100000000000000 : ℝ), (32045617940713/100000000000000 : ℝ), (3463749420191/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350575873/10000000000 : ℝ)|^2109 ≤ (33316887836757/100000000000000 : ℝ)^1597
        have hw : |(4350575873/10000000000 : ℝ)|=(4350575873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224280447/10000000000 : ℝ)|^2109 ≤ (32045617940713/100000000000000 : ℝ)^1597
        have hw : |(4224280447/10000000000 : ℝ)|=(4224280447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44805399/100000000 : ℝ)|^2109 ≤ (3463749420191/10000000000000 : ℝ)^1597
        have hw : |(44805399/100000000 : ℝ)|=(44805399/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s5_4 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059702341/5000000000 : ℝ)*x 0 + (2633205483/5000000000 : ℝ)*x 1 + (1348015449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059702341/5000000000 : ℝ)^2109 ≤ (6444174725629/50000000000000 : ℝ)^1597 := by
    have hnat : (1059702341 : ℕ)^2109*50000000000000^1597 ≤ 6444174725629^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059702341 5000000000 6444174725629 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633205483/5000000000 : ℝ)^2109 ≤ (42877757150573/100000000000000 : ℝ)^1597 := by
    have hnat : (2633205483 : ℕ)^2109*100000000000000^1597 ≤ 42877757150573^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633205483 5000000000 42877757150573 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348015449/2500000000 : ℝ)^2109 ≤ (22116946692429/50000000000000 : ℝ)^1597 := by
    have hnat : (1348015449 : ℕ)^2109*50000000000000^1597 ≤ 22116946692429^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348015449 2500000000 22116946692429 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059702341/5000000000 : ℝ), (2633205483/5000000000 : ℝ), (1348015449/2500000000 : ℝ)] ![(6444174725629/50000000000000 : ℝ), (42877757150573/100000000000000 : ℝ), (22116946692429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059702341/5000000000 : ℝ)|^2109 ≤ (6444174725629/50000000000000 : ℝ)^1597
        have hw : |(-1059702341/5000000000 : ℝ)|=(1059702341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633205483/5000000000 : ℝ)|^2109 ≤ (42877757150573/100000000000000 : ℝ)^1597
        have hw : |(2633205483/5000000000 : ℝ)|=(2633205483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348015449/2500000000 : ℝ)|^2109 ≤ (22116946692429/50000000000000 : ℝ)^1597
        have hw : |(1348015449/2500000000 : ℝ)|=(1348015449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s5_5 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312381487/10000000000 : ℝ)*x 0 + (-514369707/2500000000 : ℝ)*x 1 + (5392061797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312381487/10000000000 : ℝ)^2109 ≤ (43372722134341/100000000000000 : ℝ)^1597 := by
    have hnat : (5312381487 : ℕ)^2109*100000000000000^1597 ≤ 43372722134341^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312381487 10000000000 43372722134341 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514369707/2500000000 : ℝ)^2109 ≤ (12393384454981/100000000000000 : ℝ)^1597 := by
    have hnat : (514369707 : ℕ)^2109*100000000000000^1597 ≤ 12393384454981^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514369707 2500000000 12393384454981 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392061797/10000000000 : ℝ)^2109 ≤ (44233893395691/100000000000000 : ℝ)^1597 := by
    have hnat : (5392061797 : ℕ)^2109*100000000000000^1597 ≤ 44233893395691^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392061797 10000000000 44233893395691 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312381487/10000000000 : ℝ), (-514369707/2500000000 : ℝ), (5392061797/10000000000 : ℝ)] ![(43372722134341/100000000000000 : ℝ), (12393384454981/100000000000000 : ℝ), (44233893395691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312381487/10000000000 : ℝ)|^2109 ≤ (43372722134341/100000000000000 : ℝ)^1597
        have hw : |(5312381487/10000000000 : ℝ)|=(5312381487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514369707/2500000000 : ℝ)|^2109 ≤ (12393384454981/100000000000000 : ℝ)^1597
        have hw : |(-514369707/2500000000 : ℝ)|=(514369707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392061797/10000000000 : ℝ)|^2109 ≤ (44233893395691/100000000000000 : ℝ)^1597
        have hw : |(5392061797/10000000000 : ℝ)|=(5392061797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s5_6 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312381489/10000000000 : ℝ)*x 0 + (2696030897/5000000000 : ℝ)*x 1 + (-2057478829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312381489/10000000000 : ℝ)^2109 ≤ (8674544431181/20000000000000 : ℝ)^1597 := by
    have hnat : (5312381489 : ℕ)^2109*20000000000000^1597 ≤ 8674544431181^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312381489 10000000000 8674544431181 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696030897/5000000000 : ℝ)^2109 ≤ (44233893363191/100000000000000 : ℝ)^1597 := by
    have hnat : (2696030897 : ℕ)^2109*100000000000000^1597 ≤ 44233893363191^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696030897 5000000000 44233893363191 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2057478829/10000000000 : ℝ)^2109 ≤ (1549173057867/12500000000000 : ℝ)^1597 := by
    have hnat : (2057478829 : ℕ)^2109*12500000000000^1597 ≤ 1549173057867^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057478829 10000000000 1549173057867 12500000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312381489/10000000000 : ℝ), (2696030897/5000000000 : ℝ), (-2057478829/10000000000 : ℝ)] ![(8674544431181/20000000000000 : ℝ), (44233893363191/100000000000000 : ℝ), (1549173057867/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312381489/10000000000 : ℝ)|^2109 ≤ (8674544431181/20000000000000 : ℝ)^1597
        have hw : |(5312381489/10000000000 : ℝ)|=(5312381489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696030897/5000000000 : ℝ)|^2109 ≤ (44233893363191/100000000000000 : ℝ)^1597
        have hw : |(2696030897/5000000000 : ℝ)|=(2696030897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2057478829/10000000000 : ℝ)|^2109 ≤ (1549173057867/12500000000000 : ℝ)^1597
        have hw : |(-2057478829/10000000000 : ℝ)|=(2057478829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s5_7 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4350586089/10000000000 : ℝ)*x 0 + (1119970417/2500000000 : ℝ)*x 1 + (4224940881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350586089/10000000000 : ℝ)^2109 ≤ (1332679646137/4000000000000 : ℝ)^1597 := by
    have hnat : (4350586089 : ℕ)^2109*4000000000000^1597 ≤ 1332679646137^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350586089 10000000000 1332679646137 4000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119970417/2500000000 : ℝ)^2109 ≤ (34630774398863/100000000000000 : ℝ)^1597 := by
    have hnat : (1119970417 : ℕ)^2109*100000000000000^1597 ≤ 34630774398863^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119970417 2500000000 34630774398863 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224940881/10000000000 : ℝ)^2109 ≤ (32052234434029/100000000000000 : ℝ)^1597 := by
    have hnat : (4224940881 : ℕ)^2109*100000000000000^1597 ≤ 32052234434029^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224940881 10000000000 32052234434029 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350586089/10000000000 : ℝ), (1119970417/2500000000 : ℝ), (4224940881/10000000000 : ℝ)] ![(1332679646137/4000000000000 : ℝ), (34630774398863/100000000000000 : ℝ), (32052234434029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350586089/10000000000 : ℝ)|^2109 ≤ (1332679646137/4000000000000 : ℝ)^1597
        have hw : |(4350586089/10000000000 : ℝ)|=(4350586089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119970417/2500000000 : ℝ)|^2109 ≤ (34630774398863/100000000000000 : ℝ)^1597
        have hw : |(1119970417/2500000000 : ℝ)|=(1119970417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224940881/10000000000 : ℝ)|^2109 ≤ (32052234434029/100000000000000 : ℝ)^1597
        have hw : |(4224940881/10000000000 : ℝ)|=(4224940881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1243_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2291/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14131/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11353/100000 : ℝ) ^ (8435/2048 : ℝ) ≤ (128330301326259/1000000000000000000 : ℝ) := by
    have hpowers : (11353/100000 : ℝ)^8435 ≤ (128330301326259/1000000000000000000 : ℝ)^2048 := by
      have hnat : (11353 : ℕ)^8435*1000000000000000000^2048 ≤ 128330301326259^2048*100000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11353 100000 128330301326259 1000000000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11353/100000 : ℝ)) (X := (128330301326259/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (8435/2048 : ℝ) ≤ (6520111984205749/20000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^8435 ≤ (6520111984205749/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14237 : ℕ)^8435*20000000000000000000^2048 ≤ 6520111984205749^2048*100000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 6520111984205749 20000000000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (6520111984205749/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (500128330301326259/500000000000000000 : ℝ) ≤ (400024924236839/400000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (500128330301326259/500000000000000000 : ℝ)^2048 ≤ (400024924236839/400000000000000 : ℝ)^8435 := by
      have hnat : (500128330301326259 : ℕ)^2048*400000000000000^8435 ≤ 400024924236839^8435*500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500128330301326259 500000000000000000 400024924236839 400000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400024924236839/400000000000000 : ℝ)) (X := (500128330301326259/500000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009086718010730929/20000000000000000000 : ℝ) ≤ (5000551464086019/5000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (20009086718010730929/20000000000000000000 : ℝ)^2048 ≤ (5000551464086019/5000000000000000 : ℝ)^8435 := by
      have hnat : (20009086718010730929 : ℕ)^2048*5000000000000000^8435 ≤ 5000551464086019^8435*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009086718010730929 20000000000000000000 5000551464086019 5000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000551464086019/5000000000000000 : ℝ)) (X := (20009086718010730929/20000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006520111984205749/10000000000000000000 : ℝ) ≤ (10001582750423101/10000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (10006520111984205749/10000000000000000000 : ℝ)^2048 ≤ (10001582750423101/10000000000000000 : ℝ)^8435 := by
      have hnat : (10006520111984205749 : ℕ)^2048*10000000000000000^8435 ≤ 10001582750423101^8435*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006520111984205749 10000000000000000000 10001582750423101 10000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001582750423101/10000000000000000 : ℝ)) (X := (10006520111984205749/10000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(128330301326259/1000000000000000000 : ℝ) ≤ ((14415451096721727711/14420000000000000000 : ℝ)+2*(479822251063/288400000000000 : ℝ)*(11353/100000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (14415451096721727711/14420000000000000000 : ℝ)+2*(479822251063/288400000000000 : ℝ)*(11353/100000 : ℝ)=(400024924236839/400000000000000 : ℝ) by norm_num, show 1+2*(128330301326259/1000000000000000000 : ℝ)=(500128330301326259/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6520111984205749/20000000000000000000 : ℝ)+(128330301326259/1000000000000000000 : ℝ) ≤ ((14415451096721727711/14420000000000000000 : ℝ)+(479822251063/288400000000000 : ℝ)*((14237/100000 : ℝ)+(11353/100000 : ℝ)))^(8435/2048 : ℝ) := by
    rw [show (14415451096721727711/14420000000000000000 : ℝ)+(479822251063/288400000000000 : ℝ)*((14237/100000 : ℝ)+(11353/100000 : ℝ))=(5000551464086019/5000000000000000 : ℝ) by norm_num, show 1+(6520111984205749/20000000000000000000 : ℝ)+(128330301326259/1000000000000000000 : ℝ)=(20009086718010730929/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6520111984205749/20000000000000000000 : ℝ) ≤ ((14415451096721727711/14420000000000000000 : ℝ)+2*(479822251063/288400000000000 : ℝ)*(14237/100000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (14415451096721727711/14420000000000000000 : ℝ)+2*(479822251063/288400000000000 : ℝ)*(14237/100000 : ℝ)=(10001582750423101/10000000000000000 : ℝ) by norm_num, show 1+2*(6520111984205749/20000000000000000000 : ℝ)=(10006520111984205749/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14415451096721727711/14420000000000000000 : ℝ)*(X 1 0+X 2 0)+(479822251063/288400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14415451096721727711/14420000000000000000 : ℝ)) (alpha := (479822251063/288400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14415451096721727711/14420000000000000000 : ℝ)*(X 0 1+X 2 1)+(479822251063/288400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14415451096721727711/14420000000000000000 : ℝ)) (alpha := (479822251063/288400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14415451096721727711/14420000000000000000 : ℝ)*(X 0 2+X 1 2)+(479822251063/288400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14415451096721727711/14420000000000000000 : ℝ)) (alpha := (479822251063/288400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1059699841/5000000000 : ℝ)*X 0 0+(5392387701/10000000000 : ℝ)*X 0 1+(1053217263/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672304761/5000000000 : ℝ)*X 1 0+(-436690901/2000000000 : ℝ)*X 1 1+(2633043161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672304981/5000000000 : ℝ)*X 2 0+(5266086239/10000000000 : ℝ)*X 2 1+(-545863507/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350575873/10000000000 : ℝ)*X 0 0+(4224280447/10000000000 : ℝ)*X 0 1+(44805399/100000000 : ℝ)*X 0 2+(4350575873/10000000000 : ℝ)*X 1 0+(4224280447/10000000000 : ℝ)*X 1 1+(44805399/100000000 : ℝ)*X 1 2+(4350575873/10000000000 : ℝ)*X 2 0+(4224280447/10000000000 : ℝ)*X 2 1+(44805399/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1059702341/5000000000 : ℝ)*X 0 0+(2633205483/5000000000 : ℝ)*X 0 1+(1348015449/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312381487/10000000000 : ℝ)*X 1 0+(-514369707/2500000000 : ℝ)*X 1 1+(5392061797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312381489/10000000000 : ℝ)*X 2 0+(2696030897/5000000000 : ℝ)*X 2 1+(-2057478829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350586089/10000000000 : ℝ)*X 0 0+(1119970417/2500000000 : ℝ)*X 0 1+(4224940881/10000000000 : ℝ)*X 0 2+(4350586089/10000000000 : ℝ)*X 1 0+(1119970417/2500000000 : ℝ)*X 1 1+(4224940881/10000000000 : ℝ)*X 1 2+(4350586089/10000000000 : ℝ)*X 2 0+(1119970417/2500000000 : ℝ)*X 2 1+(4224940881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (682576802809769312057639343/90125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (469874457/50000000000000 : ℝ)*(base19) + (1715907517/100000000000000 : ℝ)*(base23) + (25672483/100000000000000 : ℝ)*(lower2) + (153432137/100000000000000 : ℝ)*(upper5) + (1477501481784371/25000000000000 : ℝ)*(major0) + (1477501481784371/25000000000000 : ℝ)*(major1) + (1477501481784371/25000000000000 : ℝ)*(major2) + (7917616723585603/100000000000000 : ℝ)*(sp0) + (494853221108087/6250000000000 : ℝ)*(sp1) + (989709918213553/12500000000000 : ℝ)*(sp2) + (3902312101498633/100000000000000 : ℝ)*(sp3) + (64338030339/100000000000000 : ℝ)*(sp4) + (5716827527/20000000000000 : ℝ)*(sp5) + (1843870479/10000000000000 : ℝ)*(sp7) + (1951165270101711/50000000000000 : ℝ)*(f.failure) + (7917681061615941/100000000000000 : ℝ)*(f.sum) + (5216237006999/1802500000000000000000000000 : ℝ)*base65 + (592748286086849317/51500000000000000000000000000000 : ℝ)*base68 + (1028682583083349317/51500000000000000000000000000000 : ℝ)*base70 + (40784271503150683/51500000000000000000000000000000 : ℝ)*base71 + (8642813197441/1802500000000000000000000000 : ℝ)*base74 + (901058091378349317/51500000000000000000000000000000 : ℝ)*base76 + (478401958475349317/51500000000000000000000000000000 : ℝ)*base78 + (1877395760775349317/51500000000000000000000000000000 : ℝ)*base80 + (2638615532517/3605000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1317523/312500000000000000000 : ℝ)*base90 + (1317523/312500000000000000000 : ℝ)*base92 + (1317523/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (869327019079629255270440523/90125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (866777467/50000000000000 : ℝ)*(base19) + (58928193/3125000000000 : ℝ)*(base23) + (12041109/6250000000000 : ℝ)*(upper3) + (3405243/5000000000000 : ℝ)*(lower4) + (98373071/50000000000000 : ℝ)*(upper5) + (742565008543277/12500000000000 : ℝ)*(major0) + (742565008543277/12500000000000 : ℝ)*(major1) + (742565008543277/12500000000000 : ℝ)*(major2) + (963599483/2000000000000 : ℝ)*(sp1) + (5163274007/10000000000000 : ℝ)*(sp2) + (3979280513477451/50000000000000 : ℝ)*(sp4) + (3979255556712909/50000000000000 : ℝ)*(sp5) + (497406719282041/6250000000000 : ℝ)*(sp6) + (1961239394105559/50000000000000 : ℝ)*(sp7) + (1961239394105559/50000000000000 : ℝ)*(f.failure) + (3979280513477451/50000000000000 : ℝ)*(f.sum) + (1150859314603/901250000000000000000000000 : ℝ)*base65 + (112950089098971579/25750000000000000000000000000000 : ℝ)*base68 + (174471958044471579/25750000000000000000000000000000 : ℝ)*base70 + (171438253157971579/25750000000000000000000000000000 : ℝ)*base72 + (4881271313487/901250000000000000000000000 : ℝ)*base74 + (158268184834971579/25750000000000000000000000000000 : ℝ)*base76 + (239426350451471579/25750000000000000000000000000000 : ℝ)*base78 + (349688025345471579/25750000000000000000000000000000 : ℝ)*base80 + (1279147648171/450625000000000000000000000 : ℝ)*base82 + (2453413/312500000000000000000 : ℝ)*base89 + (2453413/312500000000000000000 : ℝ)*base91 + (2453413/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1243_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1243_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1243_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (811/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1243_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1243_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1243_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (811/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1243_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
