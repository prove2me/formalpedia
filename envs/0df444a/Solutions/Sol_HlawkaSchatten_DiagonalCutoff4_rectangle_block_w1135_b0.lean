-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1135_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:29:06.699484+00:00
-- url     : https://prove2.me/submissions/f14adf07-b350-4cc5-a006-be4a7979c573

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
theorem support_rectangle_w1135_s0_0 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1894028517/10000000000 : ℝ)*x 0 + (6055949281/10000000000 : ℝ)*x 1 + (149362073/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1894028517/10000000000 : ℝ)^1041 ≤ (275214732429/2500000000000 : ℝ)^785 := by
    have hnat : (1894028517 : ℕ)^1041*2500000000000^785 ≤ 275214732429^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894028517 10000000000 275214732429 2500000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6055949281/10000000000 : ℝ)^1041 ≤ (6427745548589/12500000000000 : ℝ)^785 := by
    have hnat : (6055949281 : ℕ)^1041*12500000000000^785 ≤ 6427745548589^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6055949281 10000000000 6427745548589 12500000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149362073/312500000 : ℝ)^1041 ≤ (2348090393621/6250000000000 : ℝ)^785 := by
    have hnat : (149362073 : ℕ)^1041*6250000000000^785 ≤ 2348090393621^785*312500000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149362073 312500000 2348090393621 6250000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1894028517/10000000000 : ℝ), (6055949281/10000000000 : ℝ), (149362073/312500000 : ℝ)] ![(275214732429/2500000000000 : ℝ), (6427745548589/12500000000000 : ℝ), (2348090393621/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1894028517/10000000000 : ℝ)|^1041 ≤ (275214732429/2500000000000 : ℝ)^785
        have hw : |(-1894028517/10000000000 : ℝ)|=(1894028517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6055949281/10000000000 : ℝ)|^1041 ≤ (6427745548589/12500000000000 : ℝ)^785
        have hw : |(6055949281/10000000000 : ℝ)|=(6055949281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149362073/312500000 : ℝ)|^1041 ≤ (2348090393621/6250000000000 : ℝ)^785
        have hw : |(149362073/312500000 : ℝ)|=(149362073/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s0_1 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (689648397/1250000000 : ℝ)*x 0 + (-2626711917/10000000000 : ℝ)*x 1 + (4779586669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689648397/1250000000 : ℝ)^1041 ≤ (908904132129/2000000000000 : ℝ)^785 := by
    have hnat : (689648397 : ℕ)^1041*2000000000000^785 ≤ 908904132129^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689648397 1250000000 908904132129 2000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626711917/10000000000 : ℝ)^1041 ≤ (8492671807733/50000000000000 : ℝ)^785 := by
    have hnat : (2626711917 : ℕ)^1041*50000000000000^785 ≤ 8492671807733^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626711917 10000000000 8492671807733 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4779586669/10000000000 : ℝ)^1041 ≤ (37569449769057/100000000000000 : ℝ)^785 := by
    have hnat : (4779586669 : ℕ)^1041*100000000000000^785 ≤ 37569449769057^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4779586669 10000000000 37569449769057 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689648397/1250000000 : ℝ), (-2626711917/10000000000 : ℝ), (4779586669/10000000000 : ℝ)] ![(908904132129/2000000000000 : ℝ), (8492671807733/50000000000000 : ℝ), (37569449769057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689648397/1250000000 : ℝ)|^1041 ≤ (908904132129/2000000000000 : ℝ)^785
        have hw : |(689648397/1250000000 : ℝ)|=(689648397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2626711917/10000000000 : ℝ)|^1041 ≤ (8492671807733/50000000000000 : ℝ)^785
        have hw : |(-2626711917/10000000000 : ℝ)|=(2626711917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4779586669/10000000000 : ℝ)|^1041 ≤ (37569449769057/100000000000000 : ℝ)^785
        have hw : |(4779586669/10000000000 : ℝ)|=(4779586669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s0_2 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5517189357/10000000000 : ℝ)*x 0 + (597448221/1250000000 : ℝ)*x 1 + (-1313355117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517189357/10000000000 : ℝ)^1041 ≤ (11361307607509/25000000000000 : ℝ)^785 := by
    have hnat : (5517189357 : ℕ)^1041*25000000000000^785 ≤ 11361307607509^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517189357 10000000000 11361307607509 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597448221/1250000000 : ℝ)^1041 ≤ (4696180047153/12500000000000 : ℝ)^785 := by
    have hnat : (597448221 : ℕ)^1041*12500000000000^785 ≤ 4696180047153^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597448221 1250000000 4696180047153 12500000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313355117/5000000000 : ℝ)^1041 ≤ (2123166147931/12500000000000 : ℝ)^785 := by
    have hnat : (1313355117 : ℕ)^1041*12500000000000^785 ≤ 2123166147931^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313355117 5000000000 2123166147931 12500000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517189357/10000000000 : ℝ), (597448221/1250000000 : ℝ), (-1313355117/5000000000 : ℝ)] ![(11361307607509/25000000000000 : ℝ), (4696180047153/12500000000000 : ℝ), (2123166147931/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517189357/10000000000 : ℝ)|^1041 ≤ (11361307607509/25000000000000 : ℝ)^785
        have hw : |(5517189357/10000000000 : ℝ)|=(5517189357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597448221/1250000000 : ℝ)|^1041 ≤ (4696180047153/12500000000000 : ℝ)^785
        have hw : |(597448221/1250000000 : ℝ)|=(597448221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1313355117/5000000000 : ℝ)|^1041 ≤ (2123166147931/12500000000000 : ℝ)^785
        have hw : |(-1313355117/5000000000 : ℝ)|=(1313355117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s0_3 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (525194741/1250000000 : ℝ)*x 0 + (3121404719/10000000000 : ℝ)*x 1 + (226288413/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525194741/1250000000 : ℝ)^1041 ≤ (31666419131177/100000000000000 : ℝ)^785 := by
    have hnat : (525194741 : ℕ)^1041*100000000000000^785 ≤ 31666419131177^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525194741 1250000000 31666419131177 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121404719/10000000000 : ℝ)^1041 ≤ (667267939499/3125000000000 : ℝ)^785 := by
    have hnat : (3121404719 : ℕ)^1041*3125000000000^785 ≤ 667267939499^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121404719 10000000000 667267939499 3125000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226288413/400000000 : ℝ)^1041 ≤ (46981006787649/100000000000000 : ℝ)^785 := by
    have hnat : (226288413 : ℕ)^1041*100000000000000^785 ≤ 46981006787649^785*400000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226288413 400000000 46981006787649 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525194741/1250000000 : ℝ), (3121404719/10000000000 : ℝ), (226288413/400000000 : ℝ)] ![(31666419131177/100000000000000 : ℝ), (667267939499/3125000000000 : ℝ), (46981006787649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525194741/1250000000 : ℝ)|^1041 ≤ (31666419131177/100000000000000 : ℝ)^785
        have hw : |(525194741/1250000000 : ℝ)|=(525194741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121404719/10000000000 : ℝ)|^1041 ≤ (667267939499/3125000000000 : ℝ)^785
        have hw : |(3121404719/10000000000 : ℝ)|=(3121404719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226288413/400000000 : ℝ)|^1041 ≤ (46981006787649/100000000000000 : ℝ)^785
        have hw : |(226288413/400000000 : ℝ)|=(226288413/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s0_4 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1899194393/10000000000 : ℝ)*x 0 + (962503273/2000000000 : ℝ)*x 1 + (6021862233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899194393/10000000000 : ℝ)^1041 ≤ (11048424147457/100000000000000 : ℝ)^785 := by
    have hnat : (1899194393 : ℕ)^1041*100000000000000^785 ≤ 11048424147457^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899194393 10000000000 11048424147457 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962503273/2000000000 : ℝ)^1041 ≤ (37913086953319/100000000000000 : ℝ)^785 := by
    have hnat : (962503273 : ℕ)^1041*100000000000000^785 ≤ 37913086953319^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962503273 2000000000 37913086953319 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6021862233/10000000000 : ℝ)^1041 ≤ (3189905555933/6250000000000 : ℝ)^785 := by
    have hnat : (6021862233 : ℕ)^1041*6250000000000^785 ≤ 3189905555933^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6021862233 10000000000 3189905555933 6250000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1899194393/10000000000 : ℝ), (962503273/2000000000 : ℝ), (6021862233/10000000000 : ℝ)] ![(11048424147457/100000000000000 : ℝ), (37913086953319/100000000000000 : ℝ), (3189905555933/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1899194393/10000000000 : ℝ)|^1041 ≤ (11048424147457/100000000000000 : ℝ)^785
        have hw : |(-1899194393/10000000000 : ℝ)|=(1899194393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(962503273/2000000000 : ℝ)|^1041 ≤ (37913086953319/100000000000000 : ℝ)^785
        have hw : |(962503273/2000000000 : ℝ)|=(962503273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6021862233/10000000000 : ℝ)|^1041 ≤ (3189905555933/6250000000000 : ℝ)^785
        have hw : |(6021862233/10000000000 : ℝ)|=(6021862233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s0_5 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2585203071/5000000000 : ℝ)*x 0 + (-692217733/5000000000 : ℝ)*x 1 + (6021862129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585203071/5000000000 : ℝ)^1041 ≤ (10424155037157/25000000000000 : ℝ)^785 := by
    have hnat : (2585203071 : ℕ)^1041*25000000000000^785 ≤ 10424155037157^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585203071 5000000000 10424155037157 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692217733/5000000000 : ℝ)^1041 ≤ (7264892111223/100000000000000 : ℝ)^785 := by
    have hnat : (692217733 : ℕ)^1041*100000000000000^785 ≤ 7264892111223^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692217733 5000000000 7264892111223 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6021862129/10000000000 : ℝ)^1041 ≤ (51038487726017/100000000000000 : ℝ)^785 := by
    have hnat : (6021862129 : ℕ)^1041*100000000000000^785 ≤ 51038487726017^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6021862129 10000000000 51038487726017 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585203071/5000000000 : ℝ), (-692217733/5000000000 : ℝ), (6021862129/10000000000 : ℝ)] ![(10424155037157/25000000000000 : ℝ), (7264892111223/100000000000000 : ℝ), (51038487726017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585203071/5000000000 : ℝ)|^1041 ≤ (10424155037157/25000000000000 : ℝ)^785
        have hw : |(2585203071/5000000000 : ℝ)|=(2585203071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-692217733/5000000000 : ℝ)|^1041 ≤ (7264892111223/100000000000000 : ℝ)^785
        have hw : |(-692217733/5000000000 : ℝ)|=(692217733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6021862129/10000000000 : ℝ)|^1041 ≤ (51038487726017/100000000000000 : ℝ)^785
        have hw : |(6021862129/10000000000 : ℝ)|=(6021862129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s0_6 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2585203079/5000000000 : ℝ)*x 0 + (1204372427/2000000000 : ℝ)*x 1 + (-173054429/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585203079/5000000000 : ℝ)^1041 ≤ (41696620319739/100000000000000 : ℝ)^785 := by
    have hnat : (2585203079 : ℕ)^1041*100000000000000^785 ≤ 41696620319739^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585203079 5000000000 41696620319739 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204372427/2000000000 : ℝ)^1041 ≤ (25519243896727/50000000000000 : ℝ)^785 := by
    have hnat : (1204372427 : ℕ)^1041*50000000000000^785 ≤ 25519243896727^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204372427 2000000000 25519243896727 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173054429/1250000000 : ℝ)^1041 ≤ (3632445937311/50000000000000 : ℝ)^785 := by
    have hnat : (173054429 : ℕ)^1041*50000000000000^785 ≤ 3632445937311^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173054429 1250000000 3632445937311 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585203079/5000000000 : ℝ), (1204372427/2000000000 : ℝ), (-173054429/1250000000 : ℝ)] ![(41696620319739/100000000000000 : ℝ), (25519243896727/50000000000000 : ℝ), (3632445937311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585203079/5000000000 : ℝ)|^1041 ≤ (41696620319739/100000000000000 : ℝ)^785
        have hw : |(2585203079/5000000000 : ℝ)|=(2585203079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1204372427/2000000000 : ℝ)|^1041 ≤ (25519243896727/50000000000000 : ℝ)^785
        have hw : |(1204372427/2000000000 : ℝ)|=(1204372427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173054429/1250000000 : ℝ)|^1041 ≤ (3632445937311/50000000000000 : ℝ)^785
        have hw : |(-173054429/1250000000 : ℝ)|=(173054429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s0_7 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4211821653/10000000000 : ℝ)*x 0 + (5591786827/10000000000 : ℝ)*x 1 + (637825553/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211821653/10000000000 : ℝ)^1041 ≤ (1588452140041/5000000000000 : ℝ)^785 := by
    have hnat : (4211821653 : ℕ)^1041*5000000000000^785 ≤ 1588452140041^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211821653 10000000000 1588452140041 5000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5591786827/10000000000 : ℝ)^1041 ≤ (722841680991/1562500000000 : ℝ)^785 := by
    have hnat : (5591786827 : ℕ)^1041*1562500000000^785 ≤ 722841680991^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591786827 10000000000 722841680991 1562500000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637825553/2000000000 : ℝ)^1041 ≤ (10984544802133/50000000000000 : ℝ)^785 := by
    have hnat : (637825553 : ℕ)^1041*50000000000000^785 ≤ 10984544802133^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637825553 2000000000 10984544802133 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211821653/10000000000 : ℝ), (5591786827/10000000000 : ℝ), (637825553/2000000000 : ℝ)] ![(1588452140041/5000000000000 : ℝ), (722841680991/1562500000000 : ℝ), (10984544802133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211821653/10000000000 : ℝ)|^1041 ≤ (1588452140041/5000000000000 : ℝ)^785
        have hw : |(4211821653/10000000000 : ℝ)|=(4211821653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5591786827/10000000000 : ℝ)|^1041 ≤ (722841680991/1562500000000 : ℝ)^785
        have hw : |(5591786827/10000000000 : ℝ)|=(5591786827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637825553/2000000000 : ℝ)|^1041 ≤ (10984544802133/50000000000000 : ℝ)^785
        have hw : |(637825553/2000000000 : ℝ)|=(637825553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1135_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (77/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13921/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8327/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8327 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8327*1^2048 ≤ 0^2048*1^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8327/2048 : ℝ) ≤ (48199059490254891/2000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8327 ≤ (48199059490254891/2000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8327*2000000000000000000^2048 ≤ 48199059490254891^2048*5^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 48199059490254891 2000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (48199059490254891/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8327 := by
      have hnat : (1 : ℕ)^2048*1^8327 ≤ 1^8327*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2048199059490254891/2000000000000000000 : ℝ) ≤ (10058740960482607/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (2048199059490254891/2000000000000000000 : ℝ)^2048 ≤ (10058740960482607/10000000000000000 : ℝ)^8327 := by
      have hnat : (2048199059490254891 : ℕ)^2048*10000000000000000^8327 ≤ 10058740960482607^8327*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2048199059490254891 2000000000000000000 10058740960482607 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058740960482607/10000000000000000 : ℝ)) (X := (2048199059490254891/2000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1048199059490254891/1000000000000000000 : ℝ) ≤ (5058740960482607/5000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (1048199059490254891/1000000000000000000 : ℝ)^2048 ≤ (5058740960482607/5000000000000000 : ℝ)^8327 := by
      have hnat : (1048199059490254891 : ℕ)^2048*5000000000000000^8327 ≤ 5058740960482607^8327*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1048199059490254891 1000000000000000000 5058740960482607 5000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058740960482607/5000000000000000 : ℝ)) (X := (1048199059490254891/1000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58740960482607/4000000000000000 : ℝ)*(0 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(58740960482607/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48199059490254891/2000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58740960482607/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8327/2048 : ℝ) := by
    rw [show (1 : ℝ)+(58740960482607/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058740960482607/10000000000000000 : ℝ) by norm_num, show 1+(48199059490254891/2000000000000000000 : ℝ)+(0 : ℝ)=(2048199059490254891/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48199059490254891/2000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58740960482607/4000000000000000 : ℝ)*(2/5 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(58740960482607/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058740960482607/5000000000000000 : ℝ) by norm_num, show 1+2*(48199059490254891/2000000000000000000 : ℝ)=(1048199059490254891/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58740960482607/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58740960482607/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58740960482607/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58740960482607/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58740960482607/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58740960482607/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1894028517/10000000000 : ℝ)*X 0 0+(6055949281/10000000000 : ℝ)*X 0 1+(149362073/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((689648397/1250000000 : ℝ)*X 1 0+(-2626711917/10000000000 : ℝ)*X 1 1+(4779586669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5517189357/10000000000 : ℝ)*X 2 0+(597448221/1250000000 : ℝ)*X 2 1+(-1313355117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((525194741/1250000000 : ℝ)*X 0 0+(3121404719/10000000000 : ℝ)*X 0 1+(226288413/400000000 : ℝ)*X 0 2+(525194741/1250000000 : ℝ)*X 1 0+(3121404719/10000000000 : ℝ)*X 1 1+(226288413/400000000 : ℝ)*X 1 2+(525194741/1250000000 : ℝ)*X 2 0+(3121404719/10000000000 : ℝ)*X 2 1+(226288413/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1899194393/10000000000 : ℝ)*X 0 0+(962503273/2000000000 : ℝ)*X 0 1+(6021862233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2585203071/5000000000 : ℝ)*X 1 0+(-692217733/5000000000 : ℝ)*X 1 1+(6021862129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585203079/5000000000 : ℝ)*X 2 0+(1204372427/2000000000 : ℝ)*X 2 1+(-173054429/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211821653/10000000000 : ℝ)*X 0 0+(5591786827/10000000000 : ℝ)*X 0 1+(637825553/2000000000 : ℝ)*X 0 2+(4211821653/10000000000 : ℝ)*X 1 0+(5591786827/10000000000 : ℝ)*X 1 1+(637825553/2000000000 : ℝ)*X 1 2+(4211821653/10000000000 : ℝ)*X 2 0+(5591786827/10000000000 : ℝ)*X 2 1+(637825553/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83160290530916830092111/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152183/25000000000000 : ℝ)*(base1) + (255500971/50000000000000 : ℝ)*(base19) + (622350509/100000000000000 : ℝ)*(base23) + (49592049/25000000000000 : ℝ)*(base24) + (7702483/5000000000000 : ℝ)*(upper3) + (147229022522491/25000000000000 : ℝ)*(major0) + (147229022522491/25000000000000 : ℝ)*(major1) + (147229022522491/25000000000000 : ℝ)*(major2) + (195869407695659/25000000000000 : ℝ)*(sp0) + (156695646833757/20000000000000 : ℝ)*(sp1) + (391738962226011/50000000000000 : ℝ)*(sp2) + (394352326394839/100000000000000 : ℝ)*(sp3) + (1114996823/100000000000000 : ℝ)*(sp4) + (131570679/12500000000000 : ℝ)*(sp7) + (394353379569003/100000000000000 : ℝ)*(f.failure) + (783478745170727/100000000000000 : ℝ)*(f.sum) + (154635550035963/50000000000000000000000000000 : ℝ)*base66 + (351103610214037/100000000000000000000000000000 : ℝ)*base67 + (975975910814037/100000000000000000000000000000 : ℝ)*base69 + (222090487014037/100000000000000000000000000000 : ℝ)*base71 + (89001061185963/50000000000000000000000000000 : ℝ)*base74 + (302817939814037/100000000000000000000000000000 : ℝ)*base75 + (200687617614037/100000000000000000000000000000 : ℝ)*base77 + (447699368285963/100000000000000000000000000000 : ℝ)*base80 + (93123078535963/50000000000000000000000000000 : ℝ)*base82 + (5694139/2500000000000000000000 : ℝ)*base90 + (5694139/2500000000000000000000 : ℝ)*base92 + (5694139/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140925807375125987579709/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35585707/50000000000000 : ℝ)*(base1) + (1386879803/100000000000000 : ℝ)*(base19) + (1388669993/100000000000000 : ℝ)*(base23) + (150771239/100000000000000 : ℝ)*(upper3) + (162637119/100000000000000 : ℝ)*(upper5) + (310774768000071/50000000000000 : ℝ)*(major0) + (310774768000071/50000000000000 : ℝ)*(major1) + (310774768000071/50000000000000 : ℝ)*(major2) + (281330947/10000000000000 : ℝ)*(sp1) + (700457887/25000000000000 : ℝ)*(sp2) + (413446689975221/50000000000000 : ℝ)*(sp4) + (165377821717951/20000000000000 : ℝ)*(sp5) + (826889118277487/100000000000000 : ℝ)*(sp6) + (416205504148761/100000000000000 : ℝ)*(sp7) + (26012848457511/6250000000000 : ℝ)*(f.failure) + (206723327194757/25000000000000 : ℝ)*(f.sum) + (44203347565097/100000000000000000000000000000 : ℝ)*base65 + (604637434865097/200000000000000000000000000000 : ℝ)*base67 + (231687140065097/200000000000000000000000000000 : ℝ)*base69 + (103757597665097/200000000000000000000000000000 : ℝ)*base71 + (280671717565097/100000000000000000000000000000 : ℝ)*base73 + (1113090227734903/200000000000000000000000000000 : ℝ)*base76 + (227515932734903/200000000000000000000000000000 : ℝ)*base78 + (298941379065097/200000000000000000000000000000 : ℝ)*base79 + (178161615365097/100000000000000000000000000000 : ℝ)*base81 + (1104657/156250000000000000000 : ℝ)*base89 + (1104657/156250000000000000000 : ℝ)*base91 + (1104657/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1135_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (77/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13921/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1135_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1135_s1_0 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049598619/5000000000 : ℝ)*x 0 + (5703381923/10000000000 : ℝ)*x 1 + (5000802389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049598619/5000000000 : ℝ)^1041 ≤ (6308627467497/50000000000000 : ℝ)^785 := by
    have hnat : (1049598619 : ℕ)^1041*50000000000000^785 ≤ 6308627467497^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049598619 5000000000 6308627467497 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5703381923/10000000000 : ℝ)^1041 ≤ (2968135293443/6250000000000 : ℝ)^785 := by
    have hnat : (5703381923 : ℕ)^1041*6250000000000^785 ≤ 2968135293443^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5703381923 10000000000 2968135293443 6250000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5000802389/10000000000 : ℝ)^1041 ≤ (1994629017273/5000000000000 : ℝ)^785 := by
    have hnat : (5000802389 : ℕ)^1041*5000000000000^785 ≤ 1994629017273^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5000802389 10000000000 1994629017273 5000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049598619/5000000000 : ℝ), (5703381923/10000000000 : ℝ), (5000802389/10000000000 : ℝ)] ![(6308627467497/50000000000000 : ℝ), (2968135293443/6250000000000 : ℝ), (1994629017273/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049598619/5000000000 : ℝ)|^1041 ≤ (6308627467497/50000000000000 : ℝ)^785
        have hw : |(-1049598619/5000000000 : ℝ)|=(1049598619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5703381923/10000000000 : ℝ)|^1041 ≤ (2968135293443/6250000000000 : ℝ)^785
        have hw : |(5703381923/10000000000 : ℝ)|=(5703381923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5000802389/10000000000 : ℝ)|^1041 ≤ (1994629017273/5000000000000 : ℝ)^785
        have hw : |(5000802389/10000000000 : ℝ)|=(5000802389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s1_1 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2709753773/5000000000 : ℝ)*x 0 + (-2478483181/10000000000 : ℝ)*x 1 + (1000160369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709753773/5000000000 : ℝ)^1041 ≤ (22190660612173/50000000000000 : ℝ)^785 := by
    have hnat : (2709753773 : ℕ)^1041*50000000000000^785 ≤ 22190660612173^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709753773 5000000000 22190660612173 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2478483181/10000000000 : ℝ)^1041 ≤ (15726104164371/100000000000000 : ℝ)^785 := by
    have hnat : (2478483181 : ℕ)^1041*100000000000000^785 ≤ 15726104164371^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2478483181 10000000000 15726104164371 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000160369/2000000000 : ℝ)^1041 ≤ (39892574590631/100000000000000 : ℝ)^785 := by
    have hnat : (1000160369 : ℕ)^1041*100000000000000^785 ≤ 39892574590631^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000160369 2000000000 39892574590631 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709753773/5000000000 : ℝ), (-2478483181/10000000000 : ℝ), (1000160369/2000000000 : ℝ)] ![(22190660612173/50000000000000 : ℝ), (15726104164371/100000000000000 : ℝ), (39892574590631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709753773/5000000000 : ℝ)|^1041 ≤ (22190660612173/50000000000000 : ℝ)^785
        have hw : |(2709753773/5000000000 : ℝ)|=(2709753773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2478483181/10000000000 : ℝ)|^1041 ≤ (15726104164371/100000000000000 : ℝ)^785
        have hw : |(-2478483181/10000000000 : ℝ)|=(2478483181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1000160369/2000000000 : ℝ)|^1041 ≤ (39892574590631/100000000000000 : ℝ)^785
        have hw : |(1000160369/2000000000 : ℝ)|=(1000160369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s1_2 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5419509363/10000000000 : ℝ)*x 0 + (2500400111/5000000000 : ℝ)*x 1 + (-2478482877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419509363/10000000000 : ℝ)^1041 ≤ (11095335239147/25000000000000 : ℝ)^785 := by
    have hnat : (5419509363 : ℕ)^1041*25000000000000^785 ≤ 11095335239147^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419509363 10000000000 11095335239147 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2500400111/5000000000 : ℝ)^1041 ≤ (7978511484271/20000000000000 : ℝ)^785 := by
    have hnat : (2500400111 : ℕ)^1041*20000000000000^785 ≤ 7978511484271^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500400111 5000000000 7978511484271 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2478482877/10000000000 : ℝ)^1041 ≤ (7863050803217/50000000000000 : ℝ)^785 := by
    have hnat : (2478482877 : ℕ)^1041*50000000000000^785 ≤ 7863050803217^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2478482877 10000000000 7863050803217 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419509363/10000000000 : ℝ), (2500400111/5000000000 : ℝ), (-2478482877/10000000000 : ℝ)] ![(11095335239147/25000000000000 : ℝ), (7978511484271/20000000000000 : ℝ), (7863050803217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419509363/10000000000 : ℝ)|^1041 ≤ (11095335239147/25000000000000 : ℝ)^785
        have hw : |(5419509363/10000000000 : ℝ)|=(5419509363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2500400111/5000000000 : ℝ)|^1041 ≤ (7978511484271/20000000000000 : ℝ)^785
        have hw : |(2500400111/5000000000 : ℝ)|=(2500400111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2478482877/10000000000 : ℝ)|^1041 ≤ (7863050803217/50000000000000 : ℝ)^785
        have hw : |(-2478482877/10000000000 : ℝ)|=(2478482877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s1_3 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1079507817/2500000000 : ℝ)*x 0 + (229732859/625000000 : ℝ)*x 1 + (5071568377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079507817/2500000000 : ℝ)^1041 ≤ (1641788230559/5000000000000 : ℝ)^785 := by
    have hnat : (1079507817 : ℕ)^1041*5000000000000^785 ≤ 1641788230559^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079507817 2500000000 1641788230559 5000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229732859/625000000 : ℝ)^1041 ≤ (13260659440819/50000000000000 : ℝ)^785 := by
    have hnat : (229732859 : ℕ)^1041*50000000000000^785 ≤ 13260659440819^785*625000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229732859 625000000 13260659440819 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5071568377/10000000000 : ℝ)^1041 ≤ (20321458242873/50000000000000 : ℝ)^785 := by
    have hnat : (5071568377 : ℕ)^1041*50000000000000^785 ≤ 20321458242873^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071568377 10000000000 20321458242873 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079507817/2500000000 : ℝ), (229732859/625000000 : ℝ), (5071568377/10000000000 : ℝ)] ![(1641788230559/5000000000000 : ℝ), (13260659440819/50000000000000 : ℝ), (20321458242873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079507817/2500000000 : ℝ)|^1041 ≤ (1641788230559/5000000000000 : ℝ)^785
        have hw : |(1079507817/2500000000 : ℝ)|=(1079507817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229732859/625000000 : ℝ)|^1041 ≤ (13260659440819/50000000000000 : ℝ)^785
        have hw : |(229732859/625000000 : ℝ)|=(229732859/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5071568377/10000000000 : ℝ)|^1041 ≤ (20321458242873/50000000000000 : ℝ)^785
        have hw : |(5071568377/10000000000 : ℝ)|=(5071568377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s1_4 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050006727/5000000000 : ℝ)*x 0 + (1002084197/2000000000 : ℝ)*x 1 + (142339303/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050006727/5000000000 : ℝ)^1041 ≤ (3155940275997/25000000000000 : ℝ)^785 := by
    have hnat : (1050006727 : ℕ)^1041*25000000000000^785 ≤ 3155940275997^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050006727 5000000000 3155940275997 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002084197/2000000000 : ℝ)^1041 ≤ (39994364768141/100000000000000 : ℝ)^785 := by
    have hnat : (1002084197 : ℕ)^1041*100000000000000^785 ≤ 39994364768141^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002084197 2000000000 39994364768141 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142339303/250000000 : ℝ)^1041 ≤ (47381874106547/100000000000000 : ℝ)^785 := by
    have hnat : (142339303 : ℕ)^1041*100000000000000^785 ≤ 47381874106547^785*250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142339303 250000000 47381874106547 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050006727/5000000000 : ℝ), (1002084197/2000000000 : ℝ), (142339303/250000000 : ℝ)] ![(3155940275997/25000000000000 : ℝ), (39994364768141/100000000000000 : ℝ), (47381874106547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050006727/5000000000 : ℝ)|^1041 ≤ (3155940275997/25000000000000 : ℝ)^785
        have hw : |(-1050006727/5000000000 : ℝ)|=(1050006727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1002084197/2000000000 : ℝ)|^1041 ≤ (39994364768141/100000000000000 : ℝ)^785
        have hw : |(1002084197/2000000000 : ℝ)|=(1002084197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(142339303/250000000 : ℝ)|^1041 ≤ (47381874106547/100000000000000 : ℝ)^785
        have hw : |(142339303/250000000 : ℝ)|=(142339303/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s1_5 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1309860509/2500000000 : ℝ)*x 0 + (-892856293/5000000000 : ℝ)*x 1 + (5693571829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309860509/2500000000 : ℝ)^1041 ≤ (2652282603041/6250000000000 : ℝ)^785 := by
    have hnat : (1309860509 : ℕ)^1041*6250000000000^785 ≤ 2652282603041^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309860509 2500000000 2652282603041 6250000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (892856293/5000000000 : ℝ)^1041 ≤ (10181607440679/100000000000000 : ℝ)^785 := by
    have hnat : (892856293 : ℕ)^1041*100000000000000^785 ≤ 10181607440679^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892856293 5000000000 10181607440679 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5693571829/10000000000 : ℝ)^1041 ≤ (23690935447547/50000000000000 : ℝ)^785 := by
    have hnat : (5693571829 : ℕ)^1041*50000000000000^785 ≤ 23690935447547^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5693571829 10000000000 23690935447547 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309860509/2500000000 : ℝ), (-892856293/5000000000 : ℝ), (5693571829/10000000000 : ℝ)] ![(2652282603041/6250000000000 : ℝ), (10181607440679/100000000000000 : ℝ), (23690935447547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309860509/2500000000 : ℝ)|^1041 ≤ (2652282603041/6250000000000 : ℝ)^785
        have hw : |(1309860509/2500000000 : ℝ)|=(1309860509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-892856293/5000000000 : ℝ)|^1041 ≤ (10181607440679/100000000000000 : ℝ)^785
        have hw : |(-892856293/5000000000 : ℝ)|=(892856293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5693571829/10000000000 : ℝ)|^1041 ≤ (23690935447547/50000000000000 : ℝ)^785
        have hw : |(5693571829/10000000000 : ℝ)|=(5693571829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s1_6 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (654930261/1250000000 : ℝ)*x 0 + (5693572011/10000000000 : ℝ)*x 1 + (-892856123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (654930261/1250000000 : ℝ)^1041 ≤ (42436522207177/100000000000000 : ℝ)^785 := by
    have hnat : (654930261 : ℕ)^1041*100000000000000^785 ≤ 42436522207177^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654930261 1250000000 42436522207177 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5693572011/10000000000 : ℝ)^1041 ≤ (2961367056477/6250000000000 : ℝ)^785 := by
    have hnat : (5693572011 : ℕ)^1041*6250000000000^785 ≤ 2961367056477^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5693572011 10000000000 2961367056477 6250000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (892856123/5000000000 : ℝ)^1041 ≤ (101816048699/1000000000000 : ℝ)^785 := by
    have hnat : (892856123 : ℕ)^1041*1000000000000^785 ≤ 101816048699^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892856123 5000000000 101816048699 1000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(654930261/1250000000 : ℝ), (5693572011/10000000000 : ℝ), (-892856123/5000000000 : ℝ)] ![(42436522207177/100000000000000 : ℝ), (2961367056477/6250000000000 : ℝ), (101816048699/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(654930261/1250000000 : ℝ)|^1041 ≤ (42436522207177/100000000000000 : ℝ)^785
        have hw : |(654930261/1250000000 : ℝ)|=(654930261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5693572011/10000000000 : ℝ)|^1041 ≤ (2961367056477/6250000000000 : ℝ)^785
        have hw : |(5693572011/10000000000 : ℝ)|=(5693572011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-892856123/5000000000 : ℝ)|^1041 ≤ (101816048699/1000000000000 : ℝ)^785
        have hw : |(-892856123/5000000000 : ℝ)|=(892856123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s1_7 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4319649419/10000000000 : ℝ)*x 0 + (1010491933/2000000000 : ℝ)*x 1 + (3695214097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319649419/10000000000 : ℝ)^1041 ≤ (32852083403067/100000000000000 : ℝ)^785 := by
    have hnat : (4319649419 : ℕ)^1041*100000000000000^785 ≤ 32852083403067^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319649419 10000000000 32852083403067 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010491933/2000000000 : ℝ)^1041 ≤ (4043996700623/10000000000000 : ℝ)^785 := by
    have hnat : (1010491933 : ℕ)^1041*10000000000000^785 ≤ 4043996700623^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010491933 2000000000 4043996700623 10000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3695214097/10000000000 : ℝ)^1041 ≤ (6676987394189/25000000000000 : ℝ)^785 := by
    have hnat : (3695214097 : ℕ)^1041*25000000000000^785 ≤ 6676987394189^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3695214097 10000000000 6676987394189 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319649419/10000000000 : ℝ), (1010491933/2000000000 : ℝ), (3695214097/10000000000 : ℝ)] ![(32852083403067/100000000000000 : ℝ), (4043996700623/10000000000000 : ℝ), (6676987394189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319649419/10000000000 : ℝ)|^1041 ≤ (32852083403067/100000000000000 : ℝ)^785
        have hw : |(4319649419/10000000000 : ℝ)|=(4319649419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1010491933/2000000000 : ℝ)|^1041 ≤ (4043996700623/10000000000000 : ℝ)^785
        have hw : |(1010491933/2000000000 : ℝ)|=(1010491933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3695214097/10000000000 : ℝ)|^1041 ≤ (6676987394189/25000000000000 : ℝ)^785
        have hw : |(3695214097/10000000000 : ℝ)|=(3695214097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1135_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13921/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (77/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (561/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20469/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13921/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (77/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13921/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (77/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13921/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (77/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13921/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (77/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13921/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (77/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13921/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (77/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (77/20000 : ℝ) ^ (8327/2048 : ℝ) ≤ (15229350917/100000000000000000000 : ℝ) := by
    have hpowers : (77/20000 : ℝ)^8327 ≤ (15229350917/100000000000000000000 : ℝ)^2048 := by
      have hnat : (77 : ℕ)^8327*100000000000000000000^2048 ≤ 15229350917^2048*20000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77 20000 15229350917 100000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77/20000 : ℝ)) (X := (15229350917/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13921/50000 : ℝ) ^ (8327/2048 : ℝ) ≤ (110465711064168601/20000000000000000000 : ℝ) := by
    have hpowers : (13921/50000 : ℝ)^8327 ≤ (110465711064168601/20000000000000000000 : ℝ)^2048 := by
      have hnat : (13921 : ℕ)^8327*20000000000000000000^2048 ≤ 110465711064168601^2048*50000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13921 50000 110465711064168601 20000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13921/50000 : ℝ)) (X := (110465711064168601/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000015229350917/50000000000000000000 : ℝ) ≤ (10000000000749123/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (50000000015229350917/50000000000000000000 : ℝ)^2048 ≤ (10000000000749123/10000000000000000 : ℝ)^8327 := by
      have hnat : (50000000015229350917 : ℕ)^2048*10000000000000000^8327 ≤ 10000000000749123^8327*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000015229350917 50000000000000000000 10000000000749123 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000749123/10000000000000000 : ℝ)) (X := (50000000015229350917/50000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50276164285275096961/50000000000000000000 : ℝ) ≤ (10013556153668297/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (50276164285275096961/50000000000000000000 : ℝ)^2048 ≤ (10013556153668297/10000000000000000 : ℝ)^8327 := by
      have hnat : (50276164285275096961 : ℕ)^2048*10000000000000000^8327 ≤ 10013556153668297^8327*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50276164285275096961 50000000000000000000 10013556153668297 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013556153668297/10000000000000000 : ℝ)) (X := (50276164285275096961/50000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10110465711064168601/10000000000000000000 : ℝ) ≤ (10027112306587471/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (10110465711064168601/10000000000000000000 : ℝ)^2048 ≤ (10027112306587471/10000000000000000 : ℝ)^8327 := by
      have hnat : (10110465711064168601 : ℕ)^2048*10000000000000000^8327 ≤ 10027112306587471^8327*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10110465711064168601 10000000000000000000 10027112306587471 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027112306587471/10000000000000000 : ℝ)) (X := (10110465711064168601/10000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15229350917/100000000000000000000 : ℝ) ≤ ((274559561782820906231/274570000000000000000 : ℝ)+2*(6778076459587/1372850000000000 : ℝ)*(77/20000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (274559561782820906231/274570000000000000000 : ℝ)+2*(6778076459587/1372850000000000 : ℝ)*(77/20000 : ℝ)=(10000000000749123/10000000000000000 : ℝ) by norm_num, show 1+2*(15229350917/100000000000000000000 : ℝ)=(50000000015229350917/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(110465711064168601/20000000000000000000 : ℝ)+(15229350917/100000000000000000000 : ℝ) ≤ ((274559561782820906231/274570000000000000000 : ℝ)+(6778076459587/1372850000000000 : ℝ)*((13921/50000 : ℝ)+(77/20000 : ℝ)))^(8327/2048 : ℝ) := by
    rw [show (274559561782820906231/274570000000000000000 : ℝ)+(6778076459587/1372850000000000 : ℝ)*((13921/50000 : ℝ)+(77/20000 : ℝ))=(10013556153668297/10000000000000000 : ℝ) by norm_num, show 1+(110465711064168601/20000000000000000000 : ℝ)+(15229350917/100000000000000000000 : ℝ)=(50276164285275096961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(110465711064168601/20000000000000000000 : ℝ) ≤ ((274559561782820906231/274570000000000000000 : ℝ)+2*(6778076459587/1372850000000000 : ℝ)*(13921/50000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (274559561782820906231/274570000000000000000 : ℝ)+2*(6778076459587/1372850000000000 : ℝ)*(13921/50000 : ℝ)=(10027112306587471/10000000000000000 : ℝ) by norm_num, show 1+2*(110465711064168601/20000000000000000000 : ℝ)=(10110465711064168601/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (274559561782820906231/274570000000000000000 : ℝ)*(X 1 0+X 2 0)+(6778076459587/1372850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (77/20000 : ℝ)) (hi := (13921/50000 : ℝ)) (c := (274559561782820906231/274570000000000000000 : ℝ)) (alpha := (6778076459587/1372850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (274559561782820906231/274570000000000000000 : ℝ)*(X 0 1+X 2 1)+(6778076459587/1372850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (77/20000 : ℝ)) (hi := (13921/50000 : ℝ)) (c := (274559561782820906231/274570000000000000000 : ℝ)) (alpha := (6778076459587/1372850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (274559561782820906231/274570000000000000000 : ℝ)*(X 0 2+X 1 2)+(6778076459587/1372850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (77/20000 : ℝ)) (hi := (13921/50000 : ℝ)) (c := (274559561782820906231/274570000000000000000 : ℝ)) (alpha := (6778076459587/1372850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1049598619/5000000000 : ℝ)*X 0 0+(5703381923/10000000000 : ℝ)*X 0 1+(5000802389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2709753773/5000000000 : ℝ)*X 1 0+(-2478483181/10000000000 : ℝ)*X 1 1+(1000160369/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5419509363/10000000000 : ℝ)*X 2 0+(2500400111/5000000000 : ℝ)*X 2 1+(-2478482877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079507817/2500000000 : ℝ)*X 0 0+(229732859/625000000 : ℝ)*X 0 1+(5071568377/10000000000 : ℝ)*X 0 2+(1079507817/2500000000 : ℝ)*X 1 0+(229732859/625000000 : ℝ)*X 1 1+(5071568377/10000000000 : ℝ)*X 1 2+(1079507817/2500000000 : ℝ)*X 2 0+(229732859/625000000 : ℝ)*X 2 1+(5071568377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1050006727/5000000000 : ℝ)*X 0 0+(1002084197/2000000000 : ℝ)*X 0 1+(142339303/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1309860509/2500000000 : ℝ)*X 1 0+(-892856293/5000000000 : ℝ)*X 1 1+(5693571829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((654930261/1250000000 : ℝ)*X 2 0+(5693572011/10000000000 : ℝ)*X 2 1+(-892856123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319649419/10000000000 : ℝ)*X 0 0+(1010491933/2000000000 : ℝ)*X 0 1+(3695214097/10000000000 : ℝ)*X 0 2+(4319649419/10000000000 : ℝ)*X 1 0+(1010491933/2000000000 : ℝ)*X 1 1+(3695214097/10000000000 : ℝ)*X 1 2+(4319649419/10000000000 : ℝ)*X 2 0+(1010491933/2000000000 : ℝ)*X 2 1+(3695214097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106852278954000986069829611613/13728500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (481691381/100000000000000 : ℝ)*(base1) + (83223343/6250000000000 : ℝ)*(base19) + (1800636819/100000000000000 : ℝ)*(base23) + (4068647/50000000000000 : ℝ)*(base24) + (211790067/100000000000000 : ℝ)*(upper5) + (1069874171307853/100000000000000 : ℝ)*(major0) + (1069874171307853/100000000000000 : ℝ)*(major1) + (1069874171307853/100000000000000 : ℝ)*(major2) + (1423328254413297/100000000000000 : ℝ)*(sp0) + (711665727657827/50000000000000 : ℝ)*(sp1) + (1423330978115029/100000000000000 : ℝ)*(sp2) + (17910354407531/2500000000000 : ℝ)*(sp3) + (5014167227/100000000000000 : ℝ)*(sp4) + (127658487/20000000000000 : ℝ)*(sp7) + (5596994502227/781250000000 : ℝ)*(f.failure) + (1423332786889143/100000000000000 : ℝ)*(f.sum) + (383043919218263/137285000000000000000000000000 : ℝ)*base66 + (30800379402912132043/27457000000000000000000000000000000 : ℝ)*base67 + (15290582173553132043/27457000000000000000000000000000000 : ℝ)*base69 + (54083994808556132043/27457000000000000000000000000000000 : ℝ)*base71 + (405829058499963/137285000000000000000000000000 : ℝ)*base74 + (194181068371904132043/27457000000000000000000000000000000 : ℝ)*base75 + (79026168558105132043/27457000000000000000000000000000000 : ℝ)*base77 + (178407901374528132043/27457000000000000000000000000000000 : ℝ)*base79 + (133144145243637/34321250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (163827/39062500000000000000 : ℝ)*base90 + (163827/39062500000000000000 : ℝ)*base92 + (163827/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10525036053241902591099021741/1716062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39084707/50000000000000 : ℝ)*(base1) + (341474141/25000000000000 : ℝ)*(base19) + (1403310287/100000000000000 : ℝ)*(base23) + (63254969/50000000000000 : ℝ)*(upper3) + (136134251/100000000000000 : ℝ)*(upper5) + (275073959359263/25000000000000 : ℝ)*(major0) + (275073959359263/25000000000000 : ℝ)*(major1) + (275073959359263/25000000000000 : ℝ)*(major2) + (540728623/10000000000000 : ℝ)*(sp1) + (759143353/12500000000000 : ℝ)*(sp2) + (731902560632169/50000000000000 : ℝ)*(sp4) + (146379826991213/10000000000000 : ℝ)*(sp5) + (365949391659453/25000000000000 : ℝ)*(sp6) + (368393174584089/50000000000000 : ℝ)*(sp7) + (92098303417199/12500000000000 : ℝ)*(f.failure) + (365951260773731/25000000000000 : ℝ)*(f.sum) + (41590519631499/68642500000000000000000000000 : ℝ)*base65 + (24357833252884532247/6864250000000000000000000000000000 : ℝ)*base68 + (25009931507519967753/6864250000000000000000000000000000 : ℝ)*base69 + (37887847858941967753/6864250000000000000000000000000000 : ℝ)*base71 + (60698658079319/17160625000000000000000000000 : ℝ)*base74 + (3638613835789967753/6864250000000000000000000000000000 : ℝ)*base75 + (54557292471752967753/6864250000000000000000000000000000 : ℝ)*base77 + (39974316354112967753/6864250000000000000000000000000000 : ℝ)*base79 + (20382794231881/68642500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (702113/312500000000000000000 : ℝ)*base89 + (702113/312500000000000000000 : ℝ)*base91 + (702113/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1135_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13921/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (77/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (561/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20469/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1135_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1135_s2_0 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152808629/10000000000 : ℝ)*x 0 + (5512148023/10000000000 : ℝ)*x 1 + (5037063/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152808629/10000000000 : ℝ)^1041 ≤ (2609268186641/20000000000000 : ℝ)^785 := by
    have hnat : (2152808629 : ℕ)^1041*20000000000000^785 ≤ 2609268186641^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152808629 10000000000 2609268186641 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5512148023/10000000000 : ℝ)^1041 ≤ (45390170933103/100000000000000 : ℝ)^785 := by
    have hnat : (5512148023 : ℕ)^1041*100000000000000^785 ≤ 45390170933103^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512148023 10000000000 45390170933103 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5037063/9765625 : ℝ)^1041 ≤ (41563488125261/100000000000000 : ℝ)^785 := by
    have hnat : (5037063 : ℕ)^1041*100000000000000^785 ≤ 41563488125261^785*9765625^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5037063 9765625 41563488125261 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152808629/10000000000 : ℝ), (5512148023/10000000000 : ℝ), (5037063/9765625 : ℝ)] ![(2609268186641/20000000000000 : ℝ), (45390170933103/100000000000000 : ℝ), (41563488125261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152808629/10000000000 : ℝ)|^1041 ≤ (2609268186641/20000000000000 : ℝ)^785
        have hw : |(-2152808629/10000000000 : ℝ)|=(2152808629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5512148023/10000000000 : ℝ)|^1041 ≤ (45390170933103/100000000000000 : ℝ)^785
        have hw : |(5512148023/10000000000 : ℝ)|=(5512148023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5037063/9765625 : ℝ)|^1041 ≤ (41563488125261/100000000000000 : ℝ)^785
        have hw : |(5037063/9765625 : ℝ)|=(5037063/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s2_1 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (671770717/1250000000 : ℝ)*x 0 + (-2337005671/10000000000 : ℝ)*x 1 + (5157954361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671770717/1250000000 : ℝ)^1041 ≤ (43889591640497/100000000000000 : ℝ)^785 := by
    have hnat : (671770717 : ℕ)^1041*100000000000000^785 ≤ 43889591640497^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671770717 1250000000 43889591640497 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2337005671/10000000000 : ℝ)^1041 ≤ (7273450229979/50000000000000 : ℝ)^785 := by
    have hnat : (2337005671 : ℕ)^1041*50000000000000^785 ≤ 7273450229979^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337005671 10000000000 7273450229979 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5157954361/10000000000 : ℝ)^1041 ≤ (41563507883701/100000000000000 : ℝ)^785 := by
    have hnat : (5157954361 : ℕ)^1041*100000000000000^785 ≤ 41563507883701^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157954361 10000000000 41563507883701 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671770717/1250000000 : ℝ), (-2337005671/10000000000 : ℝ), (5157954361/10000000000 : ℝ)] ![(43889591640497/100000000000000 : ℝ), (7273450229979/50000000000000 : ℝ), (41563507883701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671770717/1250000000 : ℝ)|^1041 ≤ (43889591640497/100000000000000 : ℝ)^785
        have hw : |(671770717/1250000000 : ℝ)|=(671770717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2337005671/10000000000 : ℝ)|^1041 ≤ (7273450229979/50000000000000 : ℝ)^785
        have hw : |(-2337005671/10000000000 : ℝ)|=(2337005671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5157954361/10000000000 : ℝ)|^1041 ≤ (41563507883701/100000000000000 : ℝ)^785
        have hw : |(5157954361/10000000000 : ℝ)|=(5157954361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s2_2 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5374165681/10000000000 : ℝ)*x 0 + (64474429/125000000 : ℝ)*x 1 + (-584251449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374165681/10000000000 : ℝ)^1041 ≤ (43889591044843/100000000000000 : ℝ)^785 := by
    have hnat : (5374165681 : ℕ)^1041*100000000000000^785 ≤ 43889591044843^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374165681 10000000000 43889591044843 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64474429/125000000 : ℝ)^1041 ≤ (20781753722787/50000000000000 : ℝ)^785 := by
    have hnat : (64474429 : ℕ)^1041*50000000000000^785 ≤ 20781753722787^785*125000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64474429 125000000 20781753722787 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (584251449/2500000000 : ℝ)^1041 ≤ (14546901491773/100000000000000 : ℝ)^785 := by
    have hnat : (584251449 : ℕ)^1041*100000000000000^785 ≤ 14546901491773^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584251449 2500000000 14546901491773 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374165681/10000000000 : ℝ), (64474429/125000000 : ℝ), (-584251449/2500000000 : ℝ)] ![(43889591044843/100000000000000 : ℝ), (20781753722787/50000000000000 : ℝ), (14546901491773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374165681/10000000000 : ℝ)|^1041 ≤ (43889591044843/100000000000000 : ℝ)^785
        have hw : |(5374165681/10000000000 : ℝ)|=(5374165681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64474429/125000000 : ℝ)|^1041 ≤ (20781753722787/50000000000000 : ℝ)^785
        have hw : |(64474429/125000000 : ℝ)|=(64474429/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-584251449/2500000000 : ℝ)|^1041 ≤ (14546901491773/100000000000000 : ℝ)^785
        have hw : |(-584251449/2500000000 : ℝ)|=(584251449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s2_3 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2177395497/5000000000 : ℝ)*x 0 + (2008527059/5000000000 : ℝ)*x 1 + (47207451/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177395497/5000000000 : ℝ)^1041 ≤ (33206971456711/100000000000000 : ℝ)^785 := by
    have hnat : (2177395497 : ℕ)^1041*100000000000000^785 ≤ 33206971456711^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177395497 5000000000 33206971456711 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008527059/5000000000 : ℝ)^1041 ≤ (59671392257/200000000000 : ℝ)^785 := by
    have hnat : (2008527059 : ℕ)^1041*200000000000^785 ≤ 59671392257^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008527059 5000000000 59671392257 200000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47207451/100000000 : ℝ)^1041 ≤ (18478666199983/50000000000000 : ℝ)^785 := by
    have hnat : (47207451 : ℕ)^1041*50000000000000^785 ≤ 18478666199983^785*100000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47207451 100000000 18478666199983 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177395497/5000000000 : ℝ), (2008527059/5000000000 : ℝ), (47207451/100000000 : ℝ)] ![(33206971456711/100000000000000 : ℝ), (59671392257/200000000000 : ℝ), (18478666199983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177395497/5000000000 : ℝ)|^1041 ≤ (33206971456711/100000000000000 : ℝ)^785
        have hw : |(2177395497/5000000000 : ℝ)|=(2177395497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008527059/5000000000 : ℝ)|^1041 ≤ (59671392257/200000000000 : ℝ)^785
        have hw : |(2008527059/5000000000 : ℝ)|=(2008527059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(47207451/100000000 : ℝ)|^1041 ≤ (18478666199983/50000000000000 : ℝ)^785
        have hw : |(47207451/100000000 : ℝ)|=(47207451/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s2_4 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-86116529/400000000 : ℝ)*x 0 + (2580203551/5000000000 : ℝ)*x 1 + (5509668679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86116529/400000000 : ℝ)^1041 ≤ (3261795380157/25000000000000 : ℝ)^785 := by
    have hnat : (86116529 : ℕ)^1041*25000000000000^785 ≤ 3261795380157^785*400000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86116529 400000000 3261795380157 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2580203551/5000000000 : ℝ)^1041 ≤ (41589719942411/100000000000000 : ℝ)^785 := by
    have hnat : (2580203551 : ℕ)^1041*100000000000000^785 ≤ 41589719942411^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580203551 5000000000 41589719942411 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5509668679/10000000000 : ℝ)^1041 ≤ (11340774630279/25000000000000 : ℝ)^785 := by
    have hnat : (5509668679 : ℕ)^1041*25000000000000^785 ≤ 11340774630279^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509668679 10000000000 11340774630279 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86116529/400000000 : ℝ), (2580203551/5000000000 : ℝ), (5509668679/10000000000 : ℝ)] ![(3261795380157/25000000000000 : ℝ), (41589719942411/100000000000000 : ℝ), (11340774630279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86116529/400000000 : ℝ)|^1041 ≤ (3261795380157/25000000000000 : ℝ)^785
        have hw : |(-86116529/400000000 : ℝ)|=(86116529/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2580203551/5000000000 : ℝ)|^1041 ≤ (41589719942411/100000000000000 : ℝ)^785
        have hw : |(2580203551/5000000000 : ℝ)|=(2580203551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5509668679/10000000000 : ℝ)|^1041 ≤ (11340774630279/25000000000000 : ℝ)^785
        have hw : |(5509668679/10000000000 : ℝ)|=(5509668679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s2_5 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642169537/5000000000 : ℝ)*x 0 + (-397057891/2000000000 : ℝ)*x 1 + (2754834647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642169537/5000000000 : ℝ)^1041 ≤ (42919423346887/100000000000000 : ℝ)^785 := by
    have hnat : (2642169537 : ℕ)^1041*100000000000000^785 ≤ 42919423346887^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642169537 5000000000 42919423346887 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397057891/2000000000 : ℝ)^1041 ≤ (5858735697821/50000000000000 : ℝ)^785 := by
    have hnat : (397057891 : ℕ)^1041*50000000000000^785 ≤ 5858735697821^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397057891 2000000000 5858735697821 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754834647/5000000000 : ℝ)^1041 ≤ (22681552617961/50000000000000 : ℝ)^785 := by
    have hnat : (2754834647 : ℕ)^1041*50000000000000^785 ≤ 22681552617961^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754834647 5000000000 22681552617961 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642169537/5000000000 : ℝ), (-397057891/2000000000 : ℝ), (2754834647/5000000000 : ℝ)] ![(42919423346887/100000000000000 : ℝ), (5858735697821/50000000000000 : ℝ), (22681552617961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642169537/5000000000 : ℝ)|^1041 ≤ (42919423346887/100000000000000 : ℝ)^785
        have hw : |(2642169537/5000000000 : ℝ)|=(2642169537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397057891/2000000000 : ℝ)|^1041 ≤ (5858735697821/50000000000000 : ℝ)^785
        have hw : |(-397057891/2000000000 : ℝ)|=(397057891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754834647/5000000000 : ℝ)|^1041 ≤ (22681552617961/50000000000000 : ℝ)^785
        have hw : |(2754834647/5000000000 : ℝ)|=(2754834647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s2_6 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (165135553/312500000 : ℝ)*x 0 + (5509669127/10000000000 : ℝ)*x 1 + (-397058317/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165135553/312500000 : ℝ)^1041 ≤ (42919408504851/100000000000000 : ℝ)^785 := by
    have hnat : (165135553 : ℕ)^1041*100000000000000^785 ≤ 42919408504851^785*312500000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165135553 312500000 42919408504851 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509669127/10000000000 : ℝ)^1041 ≤ (5670387926569/12500000000000 : ℝ)^785 := by
    have hnat : (5509669127 : ℕ)^1041*12500000000000^785 ≤ 5670387926569^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509669127 10000000000 5670387926569 12500000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397058317/2000000000 : ℝ)^1041 ≤ (5858744033497/50000000000000 : ℝ)^785 := by
    have hnat : (397058317 : ℕ)^1041*50000000000000^785 ≤ 5858744033497^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397058317 2000000000 5858744033497 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165135553/312500000 : ℝ), (5509669127/10000000000 : ℝ), (-397058317/2000000000 : ℝ)] ![(42919408504851/100000000000000 : ℝ), (5670387926569/12500000000000 : ℝ), (5858744033497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165135553/312500000 : ℝ)|^1041 ≤ (42919408504851/100000000000000 : ℝ)^785
        have hw : |(165135553/312500000 : ℝ)|=(165135553/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509669127/10000000000 : ℝ)|^1041 ≤ (5670387926569/12500000000000 : ℝ)^785
        have hw : |(5509669127/10000000000 : ℝ)|=(5509669127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397058317/2000000000 : ℝ)|^1041 ≤ (5858744033497/50000000000000 : ℝ)^785
        have hw : |(-397058317/2000000000 : ℝ)|=(397058317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s2_7 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4354998119/10000000000 : ℝ)*x 0 + (1178967503/2500000000 : ℝ)*x 1 + (4021978207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354998119/10000000000 : ℝ)^1041 ≤ (33209065949719/100000000000000 : ℝ)^785 := by
    have hnat : (4354998119 : ℕ)^1041*100000000000000^785 ≤ 33209065949719^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354998119 10000000000 33209065949719 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1178967503/2500000000 : ℝ)^1041 ≤ (18453364456501/50000000000000 : ℝ)^785 := by
    have hnat : (1178967503 : ℕ)^1041*50000000000000^785 ≤ 18453364456501^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178967503 2500000000 18453364456501 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021978207/10000000000 : ℝ)^1041 ≤ (14942102559201/50000000000000 : ℝ)^785 := by
    have hnat : (4021978207 : ℕ)^1041*50000000000000^785 ≤ 14942102559201^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021978207 10000000000 14942102559201 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354998119/10000000000 : ℝ), (1178967503/2500000000 : ℝ), (4021978207/10000000000 : ℝ)] ![(33209065949719/100000000000000 : ℝ), (18453364456501/50000000000000 : ℝ), (14942102559201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354998119/10000000000 : ℝ)|^1041 ≤ (33209065949719/100000000000000 : ℝ)^785
        have hw : |(4354998119/10000000000 : ℝ)|=(4354998119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1178967503/2500000000 : ℝ)|^1041 ≤ (18453364456501/50000000000000 : ℝ)^785
        have hw : |(1178967503/2500000000 : ℝ)|=(1178967503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021978207/10000000000 : ℝ)|^1041 ≤ (14942102559201/50000000000000 : ℝ)^785
        have hw : |(4021978207/10000000000 : ℝ)|=(4021978207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1135_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20469/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (4519/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16523/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20469/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (561/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20469/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (561/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20469/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (561/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20469/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (561/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20469/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (561/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20469/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (561/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (561/10000 : ℝ) ^ (8327/2048 : ℝ) ≤ (204797960178167/25000000000000000000 : ℝ) := by
    have hpowers : (561/10000 : ℝ)^8327 ≤ (204797960178167/25000000000000000000 : ℝ)^2048 := by
      have hnat : (561 : ℕ)^8327*25000000000000000000^2048 ≤ 204797960178167^2048*10000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        561 10000 204797960178167 25000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (561/10000 : ℝ)) (X := (204797960178167/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20469/100000 : ℝ) ^ (8327/2048 : ℝ) ≤ (39528961211414711/25000000000000000000 : ℝ) := by
    have hpowers : (20469/100000 : ℝ)^8327 ≤ (39528961211414711/25000000000000000000 : ℝ)^2048 := by
      have hnat : (20469 : ℕ)^8327*25000000000000000000^2048 ≤ 39528961211414711^2048*100000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20469 100000 39528961211414711 25000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20469/100000 : ℝ)) (X := (39528961211414711/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500204797960178167/12500000000000000000 : ℝ) ≤ (5000020147646529/5000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (12500204797960178167/12500000000000000000 : ℝ)^2048 ≤ (5000020147646529/5000000000000000 : ℝ)^8327 := by
      have hnat : (12500204797960178167 : ℕ)^2048*5000000000000000^8327 ≤ 5000020147646529^8327*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500204797960178167 12500000000000000000 5000020147646529 5000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000020147646529/5000000000000000 : ℝ)) (X := (12500204797960178167/12500000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12519866879585796439/12500000000000000000 : ℝ) ≤ (5001953309044897/5000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (12519866879585796439/12500000000000000000 : ℝ)^2048 ≤ (5001953309044897/5000000000000000 : ℝ)^8327 := by
      have hnat : (12519866879585796439 : ℕ)^2048*5000000000000000^8327 ≤ 5001953309044897^8327*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12519866879585796439 12500000000000000000 5001953309044897 5000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001953309044897/5000000000000000 : ℝ)) (X := (12519866879585796439/12500000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12539528961211414711/12500000000000000000 : ℝ) ≤ (1000777294088653/1000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (12539528961211414711/12500000000000000000 : ℝ)^2048 ≤ (1000777294088653/1000000000000000 : ℝ)^8327 := by
      have hnat : (12539528961211414711 : ℕ)^2048*1000000000000000^8327 ≤ 1000777294088653^8327*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12539528961211414711 12500000000000000000 1000777294088653 1000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000777294088653/1000000000000000 : ℝ)) (X := (12539528961211414711/12500000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(204797960178167/25000000000000000000 : ℝ) ≤ ((24757869767663361817/24765000000000000000 : ℝ)+2*(60411293699/23217187500000 : ℝ)*(561/10000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (24757869767663361817/24765000000000000000 : ℝ)+2*(60411293699/23217187500000 : ℝ)*(561/10000 : ℝ)=(5000020147646529/5000000000000000 : ℝ) by norm_num, show 1+2*(204797960178167/25000000000000000000 : ℝ)=(12500204797960178167/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39528961211414711/25000000000000000000 : ℝ)+(204797960178167/25000000000000000000 : ℝ) ≤ ((24757869767663361817/24765000000000000000 : ℝ)+(60411293699/23217187500000 : ℝ)*((20469/100000 : ℝ)+(561/10000 : ℝ)))^(8327/2048 : ℝ) := by
    rw [show (24757869767663361817/24765000000000000000 : ℝ)+(60411293699/23217187500000 : ℝ)*((20469/100000 : ℝ)+(561/10000 : ℝ))=(5001953309044897/5000000000000000 : ℝ) by norm_num, show 1+(39528961211414711/25000000000000000000 : ℝ)+(204797960178167/25000000000000000000 : ℝ)=(12519866879585796439/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39528961211414711/25000000000000000000 : ℝ) ≤ ((24757869767663361817/24765000000000000000 : ℝ)+2*(60411293699/23217187500000 : ℝ)*(20469/100000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (24757869767663361817/24765000000000000000 : ℝ)+2*(60411293699/23217187500000 : ℝ)*(20469/100000 : ℝ)=(1000777294088653/1000000000000000 : ℝ) by norm_num, show 1+2*(39528961211414711/25000000000000000000 : ℝ)=(12539528961211414711/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24757869767663361817/24765000000000000000 : ℝ)*(X 1 0+X 2 0)+(60411293699/23217187500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (561/10000 : ℝ)) (hi := (20469/100000 : ℝ)) (c := (24757869767663361817/24765000000000000000 : ℝ)) (alpha := (60411293699/23217187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24757869767663361817/24765000000000000000 : ℝ)*(X 0 1+X 2 1)+(60411293699/23217187500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (561/10000 : ℝ)) (hi := (20469/100000 : ℝ)) (c := (24757869767663361817/24765000000000000000 : ℝ)) (alpha := (60411293699/23217187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24757869767663361817/24765000000000000000 : ℝ)*(X 0 2+X 1 2)+(60411293699/23217187500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (561/10000 : ℝ)) (hi := (20469/100000 : ℝ)) (c := (24757869767663361817/24765000000000000000 : ℝ)) (alpha := (60411293699/23217187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2152808629/10000000000 : ℝ)*X 0 0+(5512148023/10000000000 : ℝ)*X 0 1+(5037063/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((671770717/1250000000 : ℝ)*X 1 0+(-2337005671/10000000000 : ℝ)*X 1 1+(5157954361/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374165681/10000000000 : ℝ)*X 2 0+(64474429/125000000 : ℝ)*X 2 1+(-584251449/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177395497/5000000000 : ℝ)*X 0 0+(2008527059/5000000000 : ℝ)*X 0 1+(47207451/100000000 : ℝ)*X 0 2+(2177395497/5000000000 : ℝ)*X 1 0+(2008527059/5000000000 : ℝ)*X 1 1+(47207451/100000000 : ℝ)*X 1 2+(2177395497/5000000000 : ℝ)*X 2 0+(2008527059/5000000000 : ℝ)*X 2 1+(47207451/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-86116529/400000000 : ℝ)*X 0 0+(2580203551/5000000000 : ℝ)*X 0 1+(5509668679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642169537/5000000000 : ℝ)*X 1 0+(-397057891/2000000000 : ℝ)*X 1 1+(2754834647/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165135553/312500000 : ℝ)*X 2 0+(5509669127/10000000000 : ℝ)*X 2 1+(-397058317/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354998119/10000000000 : ℝ)*X 0 0+(1178967503/2500000000 : ℝ)*X 0 1+(4021978207/10000000000 : ℝ)*X 0 2+(4354998119/10000000000 : ℝ)*X 1 0+(1178967503/2500000000 : ℝ)*X 1 1+(4021978207/10000000000 : ℝ)*X 1 2+(4354998119/10000000000 : ℝ)*X 2 0+(1178967503/2500000000 : ℝ)*X 2 1+(4021978207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (169523958946921862499835381/15478125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (332187717/25000000000000 : ℝ)*(base19) + (50264191/5000000000000 : ℝ)*(base23) + (351798537/100000000000000 : ℝ)*(upper3) + (31661627/20000000000000 : ℝ)*(upper4) + (41627479/100000000000000 : ℝ)*(upper5) + (53055555518569/2500000000000 : ℝ)*(major0) + (53055555518569/2500000000000 : ℝ)*(major1) + (53055555518569/2500000000000 : ℝ)*(major2) + (112933051733573/4000000000000 : ℝ)*(sp0) + (176459256101051/6250000000000 : ℝ)*(sp1) + (352918552635483/12500000000000 : ℝ)*(sp2) + (1421085002917173/100000000000000 : ℝ)*(sp3) + (23133028359/100000000000000 : ℝ)*(sp4) + (9647117767/100000000000000 : ℝ)*(sp7) + (71054732501747/5000000000000 : ℝ)*(f.failure) + (705837356591921/25000000000000 : ℝ)*(f.sum) + (34805027023207/14859000000000000000000000000 : ℝ)*base65 + (708884908669577119/185737500000000000000000000000000 : ℝ)*base67 + (269462205596814619/185737500000000000000000000000000 : ℝ)*base69 + (1712507255783327119/185737500000000000000000000000000 : ℝ)*base71 + (24014505032083/7429500000000000000000000000 : ℝ)*base74 + (354728271165752119/185737500000000000000000000000000 : ℝ)*base75 + (688531586617572881/185737500000000000000000000000000 : ℝ)*base78 + (2105039820064164619/185737500000000000000000000000000 : ℝ)*base79 + (44295273872903/14859000000000000000000000000 : ℝ)*base82 + (499389/125000000000000000000 : ℝ)*base89 + (499389/125000000000000000000 : ℝ)*base91 + (499389/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (554979203181056079971/206375000000000000000000000 : ℝ) := by norm_num
    linear_combination (39363549/20000000000000 : ℝ)*(base19) + (354415883/100000000000000 : ℝ)*(upper2) + (51146303/50000000000000 : ℝ)*(upper3) + (7102887/20000000000000 : ℝ)*(lower4) + (430433235577351/20000000000000 : ℝ)*(major0) + (430433235577351/20000000000000 : ℝ)*(major1) + (430433235577351/20000000000000 : ℝ)*(major2) + (3226788951/50000000000000 : ℝ)*(sp0) + (2766116559/25000000000000 : ℝ)*(sp1) + (644751861/100000000000000 : ℝ)*(sp3) + (2863179917707201/100000000000000 : ℝ)*(sp4) + (1431587555000561/50000000000000 : ℝ)*(sp5) + (1431593185642551/50000000000000 : ℝ)*(sp6) + (1441145250097259/100000000000000 : ℝ)*(sp7) + (9007161842807/625000000000 : ℝ)*(f.failure) + (1431593185642551/50000000000000 : ℝ)*(f.sum) + (9957292167811/1857375000000000000000000000 : ℝ)*base65 + (1545826428521579699/1485900000000000000000000000000000 : ℝ)*base68 + (5322340578652620301/1485900000000000000000000000000000 : ℝ)*base69 + (951149077429079699/1485900000000000000000000000000000 : ℝ)*base72 + (933959633861/928687500000000000000000000 : ℝ)*base73 + (1291928946617279699/1485900000000000000000000000000000 : ℝ)*base76 + (18880750687749720301/1485900000000000000000000000000000 : ℝ)*base77 + (3771144718033020301/1485900000000000000000000000000000 : ℝ)*base79 + (3521520146399/14859000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (45141/15625000000000000000 : ℝ)*base90 + (45141/15625000000000000000 : ℝ)*base92 + (45141/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1135_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20469/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4519/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16523/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1135_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1135_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4519/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16523/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1135_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1135_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1135_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4519/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16523/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1135_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
