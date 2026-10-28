-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1152_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:36:12.951419+00:00
-- url     : https://prove2.me/submissions/1baa6709-bc6f-4fab-8e24-193d111b8a10

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
theorem support_rectangle_w1152_s3_0 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158419291/10000000000 : ℝ)*x 0 + (5428159033/10000000000 : ℝ)*x 1 + (10220727/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158419291/10000000000 : ℝ)^8345 ≤ (3277283345677/25000000000000 : ℝ)^6297 := by
    have hnat : (2158419291 : ℕ)^8345*25000000000000^6297 ≤ 3277283345677^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158419291 10000000000 3277283345677 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428159033/10000000000 : ℝ)^8345 ≤ (44499229515831/100000000000000 : ℝ)^6297 := by
    have hnat : (5428159033 : ℕ)^8345*100000000000000^6297 ≤ 44499229515831^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428159033 10000000000 44499229515831 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10220727/19531250 : ℝ)^8345 ≤ (42391637087361/100000000000000 : ℝ)^6297 := by
    have hnat : (10220727 : ℕ)^8345*100000000000000^6297 ≤ 42391637087361^6297*19531250^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10220727 19531250 42391637087361 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158419291/10000000000 : ℝ), (5428159033/10000000000 : ℝ), (10220727/19531250 : ℝ)] ![(3277283345677/25000000000000 : ℝ), (44499229515831/100000000000000 : ℝ), (42391637087361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158419291/10000000000 : ℝ)|^8345 ≤ (3277283345677/25000000000000 : ℝ)^6297
        have hw : |(-2158419291/10000000000 : ℝ)|=(2158419291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428159033/10000000000 : ℝ)|^8345 ≤ (44499229515831/100000000000000 : ℝ)^6297
        have hw : |(5428159033/10000000000 : ℝ)|=(5428159033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10220727/19531250 : ℝ)|^8345 ≤ (42391637087361/100000000000000 : ℝ)^6297
        have hw : |(10220727/19531250 : ℝ)|=(10220727/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s3_1 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338388881/2500000000 : ℝ)*x 0 + (-1129075049/5000000000 : ℝ)*x 1 + (2616506021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338388881/2500000000 : ℝ)^8345 ≤ (21845274404219/50000000000000 : ℝ)^6297 := by
    have hnat : (1338388881 : ℕ)^8345*50000000000000^6297 ≤ 21845274404219^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338388881 2500000000 21845274404219 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129075049/5000000000 : ℝ)^8345 ≤ (3479454009281/25000000000000 : ℝ)^6297 := by
    have hnat : (1129075049 : ℕ)^8345*25000000000000^6297 ≤ 3479454009281^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129075049 5000000000 3479454009281 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616506021/5000000000 : ℝ)^8345 ≤ (21195817566753/50000000000000 : ℝ)^6297 := by
    have hnat : (2616506021 : ℕ)^8345*50000000000000^6297 ≤ 21195817566753^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616506021 5000000000 21195817566753 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338388881/2500000000 : ℝ), (-1129075049/5000000000 : ℝ), (2616506021/5000000000 : ℝ)] ![(21845274404219/50000000000000 : ℝ), (3479454009281/25000000000000 : ℝ), (21195817566753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338388881/2500000000 : ℝ)|^8345 ≤ (21845274404219/50000000000000 : ℝ)^6297
        have hw : |(1338388881/2500000000 : ℝ)|=(1338388881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1129075049/5000000000 : ℝ)|^8345 ≤ (3479454009281/25000000000000 : ℝ)^6297
        have hw : |(-1129075049/5000000000 : ℝ)|=(1129075049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616506021/5000000000 : ℝ)|^8345 ≤ (21195817566753/50000000000000 : ℝ)^6297
        have hw : |(2616506021/5000000000 : ℝ)|=(2616506021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s3_2 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338388901/2500000000 : ℝ)*x 0 + (40882907/78125000 : ℝ)*x 1 + (-2258149921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338388901/2500000000 : ℝ)^8345 ≤ (43690549673661/100000000000000 : ℝ)^6297 := by
    have hnat : (1338388901 : ℕ)^8345*100000000000000^6297 ≤ 43690549673661^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338388901 2500000000 43690549673661 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40882907/78125000 : ℝ)^8345 ≤ (42391635713221/100000000000000 : ℝ)^6297 := by
    have hnat : (40882907 : ℕ)^8345*100000000000000^6297 ≤ 42391635713221^6297*78125000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40882907 78125000 42391635713221 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258149921/10000000000 : ℝ)^8345 ≤ (3479453647851/25000000000000 : ℝ)^6297 := by
    have hnat : (2258149921 : ℕ)^8345*25000000000000^6297 ≤ 3479453647851^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258149921 10000000000 3479453647851 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338388901/2500000000 : ℝ), (40882907/78125000 : ℝ), (-2258149921/10000000000 : ℝ)] ![(43690549673661/100000000000000 : ℝ), (42391635713221/100000000000000 : ℝ), (3479453647851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338388901/2500000000 : ℝ)|^8345 ≤ (43690549673661/100000000000000 : ℝ)^6297
        have hw : |(1338388901/2500000000 : ℝ)|=(1338388901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40882907/78125000 : ℝ)|^8345 ≤ (42391635713221/100000000000000 : ℝ)^6297
        have hw : |(40882907/78125000 : ℝ)|=(40882907/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2258149921/10000000000 : ℝ)|^8345 ≤ (3479453647851/25000000000000 : ℝ)^6297
        have hw : |(-2258149921/10000000000 : ℝ)|=(2258149921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s3_3 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361071611/10000000000 : ℝ)*x 0 + (1042717799/2500000000 : ℝ)*x 1 + (1139968063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361071611/10000000000 : ℝ)^8345 ≤ (33294813978277/100000000000000 : ℝ)^6297 := by
    have hnat : (4361071611 : ℕ)^8345*100000000000000^6297 ≤ 33294813978277^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361071611 10000000000 33294813978277 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042717799/2500000000 : ℝ)^8345 ≤ (3923029163747/12500000000000 : ℝ)^6297 := by
    have hnat : (1042717799 : ℕ)^8345*12500000000000^6297 ≤ 3923029163747^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042717799 2500000000 3923029163747 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139968063/2500000000 : ℝ)^8345 ≤ (17660476343299/50000000000000 : ℝ)^6297 := by
    have hnat : (1139968063 : ℕ)^8345*50000000000000^6297 ≤ 17660476343299^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139968063 2500000000 17660476343299 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361071611/10000000000 : ℝ), (1042717799/2500000000 : ℝ), (1139968063/2500000000 : ℝ)] ![(33294813978277/100000000000000 : ℝ), (3923029163747/12500000000000 : ℝ), (17660476343299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361071611/10000000000 : ℝ)|^8345 ≤ (33294813978277/100000000000000 : ℝ)^6297
        have hw : |(4361071611/10000000000 : ℝ)|=(4361071611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042717799/2500000000 : ℝ)|^8345 ≤ (3923029163747/12500000000000 : ℝ)^6297
        have hw : |(1042717799/2500000000 : ℝ)|=(1042717799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139968063/2500000000 : ℝ)|^8345 ≤ (17660476343299/50000000000000 : ℝ)^6297
        have hw : |(1139968063/2500000000 : ℝ)|=(1139968063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s3_4 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158436899/10000000000 : ℝ)*x 0 + (5233764327/10000000000 : ℝ)*x 1 + (5427402753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158436899/10000000000 : ℝ)^8345 ≤ (6554637553031/50000000000000 : ℝ)^6297 := by
    have hnat : (2158436899 : ℕ)^8345*50000000000000^6297 ≤ 6554637553031^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158436899 10000000000 6554637553031 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233764327/10000000000 : ℝ)^8345 ≤ (4239971145571/10000000000000 : ℝ)^6297 := by
    have hnat : (5233764327 : ℕ)^8345*10000000000000^6297 ≤ 4239971145571^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233764327 10000000000 4239971145571 10000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427402753/10000000000 : ℝ)^8345 ≤ (8898202684547/20000000000000 : ℝ)^6297 := by
    have hnat : (5427402753 : ℕ)^8345*20000000000000^6297 ≤ 8898202684547^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427402753 10000000000 8898202684547 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158436899/10000000000 : ℝ), (5233764327/10000000000 : ℝ), (5427402753/10000000000 : ℝ)] ![(6554637553031/50000000000000 : ℝ), (4239971145571/10000000000000 : ℝ), (8898202684547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158436899/10000000000 : ℝ)|^8345 ≤ (6554637553031/50000000000000 : ℝ)^6297
        have hw : |(-2158436899/10000000000 : ℝ)|=(2158436899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233764327/10000000000 : ℝ)|^8345 ≤ (4239971145571/10000000000000 : ℝ)^6297
        have hw : |(5233764327/10000000000 : ℝ)|=(5233764327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427402753/10000000000 : ℝ)|^8345 ≤ (8898202684547/20000000000000 : ℝ)^6297
        have hw : |(5427402753/10000000000 : ℝ)|=(5427402753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s3_5 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212163199/400000000 : ℝ)*x 0 + (-257969917/1250000000 : ℝ)*x 1 + (5427402821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212163199/400000000 : ℝ)^8345 ≤ (43156262647/100000000000 : ℝ)^6297 := by
    have hnat : (212163199 : ℕ)^8345*100000000000^6297 ≤ 43156262647^6297*400000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212163199 400000000 43156262647 100000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257969917/1250000000 : ℝ)^8345 ≤ (1544090397781/12500000000000 : ℝ)^6297 := by
    have hnat : (257969917 : ℕ)^8345*12500000000000^6297 ≤ 1544090397781^6297*1250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257969917 1250000000 1544090397781 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427402821/10000000000 : ℝ)^8345 ≤ (44491014161459/100000000000000 : ℝ)^6297 := by
    have hnat : (5427402821 : ℕ)^8345*100000000000000^6297 ≤ 44491014161459^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427402821 10000000000 44491014161459 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212163199/400000000 : ℝ), (-257969917/1250000000 : ℝ), (5427402821/10000000000 : ℝ)] ![(43156262647/100000000000 : ℝ), (1544090397781/12500000000000 : ℝ), (44491014161459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212163199/400000000 : ℝ)|^8345 ≤ (43156262647/100000000000 : ℝ)^6297
        have hw : |(212163199/400000000 : ℝ)|=(212163199/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257969917/1250000000 : ℝ)|^8345 ≤ (1544090397781/12500000000000 : ℝ)^6297
        have hw : |(-257969917/1250000000 : ℝ)|=(257969917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427402821/10000000000 : ℝ)|^8345 ≤ (44491014161459/100000000000000 : ℝ)^6297
        have hw : |(5427402821/10000000000 : ℝ)|=(5427402821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s3_6 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1326019963/2500000000 : ℝ)*x 0 + (1356850757/2500000000 : ℝ)*x 1 + (-2063759219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326019963/2500000000 : ℝ)^8345 ≤ (43156261320731/100000000000000 : ℝ)^6297 := by
    have hnat : (1326019963 : ℕ)^8345*100000000000000^6297 ≤ 43156261320731^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326019963 2500000000 43156261320731 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356850757/2500000000 : ℝ)^8345 ≤ (44491016410219/100000000000000 : ℝ)^6297 := by
    have hnat : (1356850757 : ℕ)^8345*100000000000000^6297 ≤ 44491016410219^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356850757 2500000000 44491016410219 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063759219/10000000000 : ℝ)^8345 ≤ (494108890167/4000000000000 : ℝ)^6297 := by
    have hnat : (2063759219 : ℕ)^8345*4000000000000^6297 ≤ 494108890167^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063759219 10000000000 494108890167 4000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326019963/2500000000 : ℝ), (1356850757/2500000000 : ℝ), (-2063759219/10000000000 : ℝ)] ![(43156261320731/100000000000000 : ℝ), (44491016410219/100000000000000 : ℝ), (494108890167/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326019963/2500000000 : ℝ)|^8345 ≤ (43156261320731/100000000000000 : ℝ)^6297
        have hw : |(1326019963/2500000000 : ℝ)|=(1326019963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356850757/2500000000 : ℝ)|^8345 ≤ (44491016410219/100000000000000 : ℝ)^6297
        have hw : |(1356850757/2500000000 : ℝ)|=(1356850757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2063759219/10000000000 : ℝ)|^8345 ≤ (494108890167/4000000000000 : ℝ)^6297
        have hw : |(-2063759219/10000000000 : ℝ)|=(2063759219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s3_7 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174444269/400000000 : ℝ)*x 0 + (1139593289/2500000000 : ℝ)*x 1 + (260773663/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174444269/400000000 : ℝ)^8345 ≤ (6659033849387/20000000000000 : ℝ)^6297 := by
    have hnat : (174444269 : ℕ)^8345*20000000000000^6297 ≤ 6659033849387^6297*400000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174444269 400000000 6659033849387 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139593289/2500000000 : ℝ)^8345 ≤ (8826391203289/25000000000000 : ℝ)^6297 := by
    have hnat : (1139593289 : ℕ)^8345*25000000000000^6297 ≤ 8826391203289^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139593289 2500000000 8826391203289 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260773663/625000000 : ℝ)^8345 ≤ (31399265937023/100000000000000 : ℝ)^6297 := by
    have hnat : (260773663 : ℕ)^8345*100000000000000^6297 ≤ 31399265937023^6297*625000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260773663 625000000 31399265937023 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174444269/400000000 : ℝ), (1139593289/2500000000 : ℝ), (260773663/625000000 : ℝ)] ![(6659033849387/20000000000000 : ℝ), (8826391203289/25000000000000 : ℝ), (31399265937023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174444269/400000000 : ℝ)|^8345 ≤ (6659033849387/20000000000000 : ℝ)^6297
        have hw : |(174444269/400000000 : ℝ)|=(174444269/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1139593289/2500000000 : ℝ)|^8345 ≤ (8826391203289/25000000000000 : ℝ)^6297
        have hw : |(1139593289/2500000000 : ℝ)|=(1139593289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260773663/625000000 : ℝ)|^8345 ≤ (31399265937023/100000000000000 : ℝ)^6297
        have hw : |(260773663/625000000 : ℝ)|=(260773663/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1152_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1823/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1333/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7397/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1823/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1823/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1823/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1823/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1823/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1823/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1823/20000 : ℝ) ^ (1043/256 : ℝ) ≤ (5778580032059219/100000000000000000000 : ℝ) := by
    have hpowers : (1823/20000 : ℝ)^1043 ≤ (5778580032059219/100000000000000000000 : ℝ)^256 := by
      have hnat : (1823 : ℕ)^1043*100000000000000000000^256 ≤ 5778580032059219^256*20000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1823 20000 5778580032059219 100000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1823/20000 : ℝ)) (X := (5778580032059219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hpowhi : (16473/100000 : ℝ) ^ (1043/256 : ℝ) ≤ (12882217817243151/20000000000000000000 : ℝ) := by
    have hpowers : (16473/100000 : ℝ)^1043 ≤ (12882217817243151/20000000000000000000 : ℝ)^256 := by
      have hnat : (16473 : ℕ)^1043*20000000000000000000^256 ≤ 12882217817243151^256*100000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16473 100000 12882217817243151 20000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16473/100000 : ℝ)) (X := (12882217817243151/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005778580032059219/50000000000000000000 : ℝ) ≤ (10000283653305973/10000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50005778580032059219/50000000000000000000 : ℝ)^256 ≤ (10000283653305973/10000000000000000 : ℝ)^1043 := by
      have hnat : (50005778580032059219 : ℕ)^256*10000000000000000^1043 ≤ 10000283653305973^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005778580032059219 50000000000000000000 10000283653305973 10000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283653305973/10000000000000000 : ℝ)) (X := (50005778580032059219/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50035094834559137487/50000000000000000000 : ℝ) ≤ (10001722320134401/10000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50035094834559137487/50000000000000000000 : ℝ)^256 ≤ (10001722320134401/10000000000000000 : ℝ)^1043 := by
      have hnat : (50035094834559137487 : ℕ)^256*10000000000000000^1043 ≤ 10001722320134401^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035094834559137487 50000000000000000000 10001722320134401 10000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001722320134401/10000000000000000 : ℝ)) (X := (50035094834559137487/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10012882217817243151/10000000000000000000 : ℝ) ≤ (10003160986962829/10000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (10012882217817243151/10000000000000000000 : ℝ)^256 ≤ (10003160986962829/10000000000000000 : ℝ)^1043 := by
      have hnat : (10012882217817243151 : ℕ)^256*10000000000000000^1043 ≤ 10003160986962829^1043*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10012882217817243151 10000000000000000000 10003160986962829 10000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003160986962829/10000000000000000 : ℝ)) (X := (10012882217817243151/10000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5778580032059219/100000000000000000000 : ℝ) ≤ ((36777930112371553447/36790000000000000000 : ℝ)+2*(359666707107/183950000000000 : ℝ)*(1823/20000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (36777930112371553447/36790000000000000000 : ℝ)+2*(359666707107/183950000000000 : ℝ)*(1823/20000 : ℝ)=(10000283653305973/10000000000000000 : ℝ) by norm_num, show 1+2*(5778580032059219/100000000000000000000 : ℝ)=(50005778580032059219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12882217817243151/20000000000000000000 : ℝ)+(5778580032059219/100000000000000000000 : ℝ) ≤ ((36777930112371553447/36790000000000000000 : ℝ)+(359666707107/183950000000000 : ℝ)*((16473/100000 : ℝ)+(1823/20000 : ℝ)))^(1043/256 : ℝ) := by
    rw [show (36777930112371553447/36790000000000000000 : ℝ)+(359666707107/183950000000000 : ℝ)*((16473/100000 : ℝ)+(1823/20000 : ℝ))=(10001722320134401/10000000000000000 : ℝ) by norm_num, show 1+(12882217817243151/20000000000000000000 : ℝ)+(5778580032059219/100000000000000000000 : ℝ)=(50035094834559137487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12882217817243151/20000000000000000000 : ℝ) ≤ ((36777930112371553447/36790000000000000000 : ℝ)+2*(359666707107/183950000000000 : ℝ)*(16473/100000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (36777930112371553447/36790000000000000000 : ℝ)+2*(359666707107/183950000000000 : ℝ)*(16473/100000 : ℝ)=(10003160986962829/10000000000000000 : ℝ) by norm_num, show 1+2*(12882217817243151/20000000000000000000 : ℝ)=(10012882217817243151/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36777930112371553447/36790000000000000000 : ℝ)*(X 1 0+X 2 0)+(359666707107/183950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1823/20000 : ℝ)) (hi := (16473/100000 : ℝ)) (c := (36777930112371553447/36790000000000000000 : ℝ)) (alpha := (359666707107/183950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36777930112371553447/36790000000000000000 : ℝ)*(X 0 1+X 2 1)+(359666707107/183950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1823/20000 : ℝ)) (hi := (16473/100000 : ℝ)) (c := (36777930112371553447/36790000000000000000 : ℝ)) (alpha := (359666707107/183950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36777930112371553447/36790000000000000000 : ℝ)*(X 0 2+X 1 2)+(359666707107/183950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1823/20000 : ℝ)) (hi := (16473/100000 : ℝ)) (c := (36777930112371553447/36790000000000000000 : ℝ)) (alpha := (359666707107/183950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2158419291/10000000000 : ℝ)*X 0 0+(5428159033/10000000000 : ℝ)*X 0 1+(10220727/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338388881/2500000000 : ℝ)*X 1 0+(-1129075049/5000000000 : ℝ)*X 1 1+(2616506021/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338388901/2500000000 : ℝ)*X 2 0+(40882907/78125000 : ℝ)*X 2 1+(-2258149921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361071611/10000000000 : ℝ)*X 0 0+(1042717799/2500000000 : ℝ)*X 0 1+(1139968063/2500000000 : ℝ)*X 0 2+(4361071611/10000000000 : ℝ)*X 1 0+(1042717799/2500000000 : ℝ)*X 1 1+(1139968063/2500000000 : ℝ)*X 1 2+(4361071611/10000000000 : ℝ)*X 2 0+(1042717799/2500000000 : ℝ)*X 2 1+(1139968063/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2158436899/10000000000 : ℝ)*X 0 0+(5233764327/10000000000 : ℝ)*X 0 1+(5427402753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212163199/400000000 : ℝ)*X 1 0+(-257969917/1250000000 : ℝ)*X 1 1+(5427402821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326019963/2500000000 : ℝ)*X 2 0+(1356850757/2500000000 : ℝ)*X 2 1+(-2063759219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174444269/400000000 : ℝ)*X 0 0+(1139593289/2500000000 : ℝ)*X 0 1+(260773663/625000000 : ℝ)*X 0 2+(174444269/400000000 : ℝ)*X 1 0+(1139593289/2500000000 : ℝ)*X 1 1+(260773663/625000000 : ℝ)*X 1 2+(174444269/400000000 : ℝ)*X 2 0+(1139593289/2500000000 : ℝ)*X 2 1+(260773663/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16247505561577526685783899589/1839500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2106715483/100000000000000 : ℝ)*(base19) + (79957609/4000000000000 : ℝ)*(base23) + (4934671/5000000000000 : ℝ)*(lower2) + (41682477/25000000000000 : ℝ)*(upper3) + (114286891/50000000000000 : ℝ)*(upper5) + (480946362091983/12500000000000 : ℝ)*(major0) + (480946362091983/12500000000000 : ℝ)*(major1) + (769514179347173/20000000000000 : ℝ)*(major2) + (2562190392936913/50000000000000 : ℝ)*(sp0) + (819906714679/16000000000 : ℝ)*(sp1) + (160138033578719/3125000000000 : ℝ)*(sp2) + (642676160099257/25000000000000 : ℝ)*(sp3) + (38287585407/100000000000000 : ℝ)*(sp4) + (4446299147/25000000000000 : ℝ)*(sp7) + (160670151599601/6250000000000 : ℝ)*(f.failure) + (5124419073459233/100000000000000 : ℝ)*(f.sum) + (25268796920713/4598750000000000000000000000 : ℝ)*base66 + (3003499206306034599/459875000000000000000000000000000 : ℝ)*base68 + (581533292513224669/735800000000000000000000000000000 : ℝ)*base70 + (2839350432775409599/459875000000000000000000000000000 : ℝ)*base72 + (21378731847817/18395000000000000000000000000 : ℝ)*base74 + (4719792431592224669/735800000000000000000000000000000 : ℝ)*base76 + (1001927696608877/35375000000000000000000000000000 : ℝ)*base77 + (752569437372391123/35375000000000000000000000000000 : ℝ)*base80 + (18397477217/574843750000000000000000000 : ℝ)*base82 + (2462829/312500000000000000000 : ℝ)*base89 + (2462829/312500000000000000000 : ℝ)*base91 + (662171/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130666469566117301704119/18395000000000000000000000000 : ℝ) := by norm_num
    linear_combination (706805943/50000000000000 : ℝ)*(base19) + (762684189/50000000000000 : ℝ)*(base23) + (88096591/50000000000000 : ℝ)*(upper3) + (903173/1000000000000 : ℝ)*(lower4) + (149894339/100000000000000 : ℝ)*(upper5) + (1938742815092697/50000000000000 : ℝ)*(major0) + (1938742815092697/50000000000000 : ℝ)*(major1) + (1938742815092697/50000000000000 : ℝ)*(major2) + (649865661/2500000000000 : ℝ)*(sp1) + (6511855519/20000000000000 : ℝ)*(sp2) + (5164261318179761/100000000000000 : ℝ)*(sp4) + (1291058477485359/25000000000000 : ℝ)*(sp5) + (5164227233533789/100000000000000 : ℝ)*(sp6) + (129535485270603/5000000000000 : ℝ)*(sp7) + (129535485270603/5000000000000 : ℝ)*(f.failure) + (5164261318179761/100000000000000 : ℝ)*(f.sum) + (90642185140279/18395000000000000000000000000 : ℝ)*base66 + (813628210879552043/141500000000000000000000000000000 : ℝ)*base67 + (17761732919447957/141500000000000000000000000000000 : ℝ)*base70 + (154465964969947957/141500000000000000000000000000000 : ℝ)*base72 + (19902774245141/4598750000000000000000000000 : ℝ)*base74 + (873334601556052043/141500000000000000000000000000000 : ℝ)*base75 + (665452597111947957/141500000000000000000000000000000 : ℝ)*base78 + (598475145232052043/141500000000000000000000000000000 : ℝ)*base79 + (53612080835407/9197500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (990687/250000000000000000000 : ℝ)*base89 + (990687/250000000000000000000 : ℝ)*base91 + (990687/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1152_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1823/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1333/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1152_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1152_s4_0 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2161342389/10000000000 : ℝ)*x 0 + (5401420537/10000000000 : ℝ)*x 1 + (5257838147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161342389/10000000000 : ℝ)^8345 ≤ (6566332988199/50000000000000 : ℝ)^6297 := by
    have hnat : (2161342389 : ℕ)^8345*50000000000000^6297 ≤ 6566332988199^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161342389 10000000000 6566332988199 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401420537/10000000000 : ℝ)^8345 ≤ (44208973559303/100000000000000 : ℝ)^6297 := by
    have hnat : (5401420537 : ℕ)^8345*100000000000000^6297 ≤ 44208973559303^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401420537 10000000000 44208973559303 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257838147/10000000000 : ℝ)^8345 ≤ (8531672089197/20000000000000 : ℝ)^6297 := by
    have hnat : (5257838147 : ℕ)^8345*20000000000000^6297 ≤ 8531672089197^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257838147 10000000000 8531672089197 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2161342389/10000000000 : ℝ), (5401420537/10000000000 : ℝ), (5257838147/10000000000 : ℝ)] ![(6566332988199/50000000000000 : ℝ), (44208973559303/100000000000000 : ℝ), (8531672089197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2161342389/10000000000 : ℝ)|^8345 ≤ (6566332988199/50000000000000 : ℝ)^6297
        have hw : |(-2161342389/10000000000 : ℝ)|=(2161342389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401420537/10000000000 : ℝ)|^8345 ≤ (44208973559303/100000000000000 : ℝ)^6297
        have hw : |(5401420537/10000000000 : ℝ)|=(5401420537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257838147/10000000000 : ℝ)|^8345 ≤ (8531672089197/20000000000000 : ℝ)^6297
        have hw : |(5257838147/10000000000 : ℝ)|=(5257838147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s4_1 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346871209/10000000000 : ℝ)*x 0 + (-89372087/400000000 : ℝ)*x 1 + (5257838623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346871209/10000000000 : ℝ)^8345 ≤ (21809135370523/50000000000000 : ℝ)^6297 := by
    have hnat : (5346871209 : ℕ)^8345*50000000000000^6297 ≤ 21809135370523^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346871209 10000000000 21809135370523 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89372087/400000000 : ℝ)^8345 ≤ (1715420459211/12500000000000 : ℝ)^6297 := by
    have hnat : (89372087 : ℕ)^8345*12500000000000^6297 ≤ 1715420459211^6297*400000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89372087 400000000 1715420459211 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257838623/10000000000 : ℝ)^8345 ≤ (42658365563941/100000000000000 : ℝ)^6297 := by
    have hnat : (5257838623 : ℕ)^8345*100000000000000^6297 ≤ 42658365563941^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257838623 10000000000 42658365563941 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346871209/10000000000 : ℝ), (-89372087/400000000 : ℝ), (5257838623/10000000000 : ℝ)] ![(21809135370523/50000000000000 : ℝ), (1715420459211/12500000000000 : ℝ), (42658365563941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346871209/10000000000 : ℝ)|^8345 ≤ (21809135370523/50000000000000 : ℝ)^6297
        have hw : |(5346871209/10000000000 : ℝ)|=(5346871209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89372087/400000000 : ℝ)|^8345 ≤ (1715420459211/12500000000000 : ℝ)^6297
        have hw : |(-89372087/400000000 : ℝ)|=(89372087/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257838623/10000000000 : ℝ)|^8345 ≤ (42658365563941/100000000000000 : ℝ)^6297
        have hw : |(5257838623/10000000000 : ℝ)|=(5257838623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s4_2 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673435627/5000000000 : ℝ)*x 0 + (1314459569/2500000000 : ℝ)*x 1 + (-1117151287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673435627/5000000000 : ℝ)^8345 ≤ (2726141951721/6250000000000 : ℝ)^6297 := by
    have hnat : (2673435627 : ℕ)^8345*6250000000000^6297 ≤ 2726141951721^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673435627 5000000000 2726141951721 6250000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314459569/2500000000 : ℝ)^8345 ≤ (21329180916497/50000000000000 : ℝ)^6297 := by
    have hnat : (1314459569 : ℕ)^8345*50000000000000^6297 ≤ 21329180916497^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314459569 2500000000 21329180916497 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117151287/5000000000 : ℝ)^8345 ≤ (274467338429/2000000000000 : ℝ)^6297 := by
    have hnat : (1117151287 : ℕ)^8345*2000000000000^6297 ≤ 274467338429^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117151287 5000000000 274467338429 2000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673435627/5000000000 : ℝ), (1314459569/2500000000 : ℝ), (-1117151287/5000000000 : ℝ)] ![(2726141951721/6250000000000 : ℝ), (21329180916497/50000000000000 : ℝ), (274467338429/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673435627/5000000000 : ℝ)|^8345 ≤ (2726141951721/6250000000000 : ℝ)^6297
        have hw : |(2673435627/5000000000 : ℝ)|=(2673435627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314459569/2500000000 : ℝ)|^8345 ≤ (21329180916497/50000000000000 : ℝ)^6297
        have hw : |(1314459569/2500000000 : ℝ)|=(1314459569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1117151287/5000000000 : ℝ)|^8345 ≤ (274467338429/2000000000000 : ℝ)^6297
        have hw : |(-1117151287/5000000000 : ℝ)|=(1117151287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s4_3 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181408353/5000000000 : ℝ)*x 0 + (168881543/400000000 : ℝ)*x 1 + (4508253227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181408353/5000000000 : ℝ)^8345 ≤ (33312471239963/100000000000000 : ℝ)^6297 := by
    have hnat : (2181408353 : ℕ)^8345*100000000000000^6297 ≤ 33312471239963^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181408353 5000000000 33312471239963 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168881543/400000000 : ℝ)^8345 ≤ (6379096757021/20000000000000 : ℝ)^6297 := by
    have hnat : (168881543 : ℕ)^8345*20000000000000^6297 ≤ 6379096757021^6297*400000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168881543 400000000 6379096757021 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508253227/10000000000 : ℝ)^8345 ≤ (34792044959347/100000000000000 : ℝ)^6297 := by
    have hnat : (4508253227 : ℕ)^8345*100000000000000^6297 ≤ 34792044959347^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508253227 10000000000 34792044959347 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181408353/5000000000 : ℝ), (168881543/400000000 : ℝ), (4508253227/10000000000 : ℝ)] ![(33312471239963/100000000000000 : ℝ), (6379096757021/20000000000000 : ℝ), (34792044959347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181408353/5000000000 : ℝ)|^8345 ≤ (33312471239963/100000000000000 : ℝ)^6297
        have hw : |(2181408353/5000000000 : ℝ)|=(2181408353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168881543/400000000 : ℝ)|^8345 ≤ (6379096757021/20000000000000 : ℝ)^6297
        have hw : |(168881543/400000000 : ℝ)|=(168881543/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508253227/10000000000 : ℝ)|^8345 ≤ (34792044959347/100000000000000 : ℝ)^6297
        have hw : |(4508253227/10000000000 : ℝ)|=(4508253227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s4_4 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-27016869/125000000 : ℝ)*x 0 + (5258246059/10000000000 : ℝ)*x 1 + (5401010879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27016869/125000000 : ℝ)^8345 ≤ (820795212353/6250000000000 : ℝ)^6297 := by
    have hnat : (27016869 : ℕ)^8345*6250000000000^6297 ≤ 820795212353^6297*125000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27016869 125000000 820795212353 6250000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258246059/10000000000 : ℝ)^8345 ≤ (42662746374559/100000000000000 : ℝ)^6297 := by
    have hnat : (5258246059 : ℕ)^8345*100000000000000^6297 ≤ 42662746374559^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258246059 10000000000 42662746374559 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401010879/10000000000 : ℝ)^8345 ≤ (44204530202671/100000000000000 : ℝ)^6297 := by
    have hnat : (5401010879 : ℕ)^8345*100000000000000^6297 ≤ 44204530202671^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401010879 10000000000 44204530202671 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27016869/125000000 : ℝ), (5258246059/10000000000 : ℝ), (5401010879/10000000000 : ℝ)] ![(820795212353/6250000000000 : ℝ), (42662746374559/100000000000000 : ℝ), (44204530202671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27016869/125000000 : ℝ)|^8345 ≤ (820795212353/6250000000000 : ℝ)^6297
        have hw : |(-27016869/125000000 : ℝ)|=(27016869/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258246059/10000000000 : ℝ)|^8345 ≤ (42662746374559/100000000000000 : ℝ)^6297
        have hw : |(5258246059/10000000000 : ℝ)|=(5258246059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401010879/10000000000 : ℝ)|^8345 ≤ (44204530202671/100000000000000 : ℝ)^6297
        have hw : |(5401010879/10000000000 : ℝ)|=(5401010879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s4_5 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531046933/1000000000 : ℝ)*x 0 + (-261391223/1250000000 : ℝ)*x 1 + (675126361/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531046933/1000000000 : ℝ)^8345 ≤ (5403146307629/12500000000000 : ℝ)^6297 := by
    have hnat : (531046933 : ℕ)^8345*12500000000000^6297 ≤ 5403146307629^6297*1000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531046933 1000000000 5403146307629 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261391223/1250000000 : ℝ)^8345 ≤ (12570299224393/100000000000000 : ℝ)^6297 := by
    have hnat : (261391223 : ℕ)^8345*100000000000000^6297 ≤ 12570299224393^6297*1250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261391223 1250000000 12570299224393 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675126361/1250000000 : ℝ)^8345 ≤ (345347892971/781250000000 : ℝ)^6297 := by
    have hnat : (675126361 : ℕ)^8345*781250000000^6297 ≤ 345347892971^6297*1250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675126361 1250000000 345347892971 781250000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531046933/1000000000 : ℝ), (-261391223/1250000000 : ℝ), (675126361/1250000000 : ℝ)] ![(5403146307629/12500000000000 : ℝ), (12570299224393/100000000000000 : ℝ), (345347892971/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531046933/1000000000 : ℝ)|^8345 ≤ (5403146307629/12500000000000 : ℝ)^6297
        have hw : |(531046933/1000000000 : ℝ)|=(531046933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261391223/1250000000 : ℝ)|^8345 ≤ (12570299224393/100000000000000 : ℝ)^6297
        have hw : |(-261391223/1250000000 : ℝ)|=(261391223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675126361/1250000000 : ℝ)|^8345 ≤ (345347892971/781250000000 : ℝ)^6297
        have hw : |(675126361/1250000000 : ℝ)|=(675126361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s4_6 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310469311/10000000000 : ℝ)*x 0 + (5401011099/10000000000 : ℝ)*x 1 + (-1045564761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310469311/10000000000 : ℝ)^8345 ≤ (43225170256081/100000000000000 : ℝ)^6297 := by
    have hnat : (5310469311 : ℕ)^8345*100000000000000^6297 ≤ 43225170256081^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310469311 10000000000 43225170256081 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401011099/10000000000 : ℝ)^8345 ≤ (5525566573609/12500000000000 : ℝ)^6297 := by
    have hnat : (5401011099 : ℕ)^8345*12500000000000^6297 ≤ 5525566573609^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401011099 10000000000 5525566573609 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045564761/5000000000 : ℝ)^8345 ≤ (628514856861/5000000000000 : ℝ)^6297 := by
    have hnat : (1045564761 : ℕ)^8345*5000000000000^6297 ≤ 628514856861^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045564761 5000000000 628514856861 5000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310469311/10000000000 : ℝ), (5401011099/10000000000 : ℝ), (-1045564761/5000000000 : ℝ)] ![(43225170256081/100000000000000 : ℝ), (5525566573609/12500000000000 : ℝ), (628514856861/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310469311/10000000000 : ℝ)|^8345 ≤ (43225170256081/100000000000000 : ℝ)^6297
        have hw : |(5310469311/10000000000 : ℝ)|=(5310469311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401011099/10000000000 : ℝ)|^8345 ≤ (5525566573609/12500000000000 : ℝ)^6297
        have hw : |(5401011099/10000000000 : ℝ)|=(5401011099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1045564761/5000000000 : ℝ)|^8345 ≤ (628514856861/5000000000000 : ℝ)^6297
        have hw : |(-1045564761/5000000000 : ℝ)|=(1045564761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s4_7 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362830671/10000000000 : ℝ)*x 0 + (563430009/1250000000 : ℝ)*x 1 + (4222855099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362830671/10000000000 : ℝ)^8345 ≤ (33312612550223/100000000000000 : ℝ)^6297 := by
    have hnat : (4362830671 : ℕ)^8345*100000000000000^6297 ≤ 33312612550223^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362830671 10000000000 33312612550223 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563430009/1250000000 : ℝ)^8345 ≤ (8695932189963/25000000000000 : ℝ)^6297 := by
    have hnat : (563430009 : ℕ)^8345*25000000000000^6297 ≤ 8695932189963^6297*1250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563430009 1250000000 8695932189963 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222855099/10000000000 : ℝ)^8345 ≤ (6380731736297/20000000000000 : ℝ)^6297 := by
    have hnat : (4222855099 : ℕ)^8345*20000000000000^6297 ≤ 6380731736297^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222855099 10000000000 6380731736297 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362830671/10000000000 : ℝ), (563430009/1250000000 : ℝ), (4222855099/10000000000 : ℝ)] ![(33312612550223/100000000000000 : ℝ), (8695932189963/25000000000000 : ℝ), (6380731736297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362830671/10000000000 : ℝ)|^8345 ≤ (33312612550223/100000000000000 : ℝ)^6297
        have hw : |(4362830671/10000000000 : ℝ)|=(4362830671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563430009/1250000000 : ℝ)|^8345 ≤ (8695932189963/25000000000000 : ℝ)^6297
        have hw : |(563430009/1250000000 : ℝ)|=(563430009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222855099/10000000000 : ℝ)|^8345 ≤ (6380731736297/20000000000000 : ℝ)^6297
        have hw : |(4222855099/10000000000 : ℝ)|=(4222855099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1152_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1333/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5597/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1333/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1333/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1333/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1333/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1333/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1333/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1333/12500 : ℝ) ^ (1043/256 : ℝ) ≤ (684563927430463/6250000000000000000 : ℝ) := by
    have hpowers : (1333/12500 : ℝ)^1043 ≤ (684563927430463/6250000000000000000 : ℝ)^256 := by
      have hnat : (1333 : ℕ)^1043*6250000000000000000^256 ≤ 684563927430463^256*12500^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1333 12500 684563927430463 6250000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1333/12500 : ℝ)) (X := (684563927430463/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7397/50000 : ℝ) ^ (1043/256 : ℝ) ≤ (8313372582426947/20000000000000000000 : ℝ) := by
    have hpowers : (7397/50000 : ℝ)^1043 ≤ (8313372582426947/20000000000000000000 : ℝ)^256 := by
      have hnat : (7397 : ℕ)^1043*20000000000000000000^256 ≤ 8313372582426947^256*50000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7397 50000 8313372582426947 20000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7397/50000 : ℝ)) (X := (8313372582426947/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125684563927430463/3125000000000000000 : ℝ) ≤ (2500134407580913/2500000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (3125684563927430463/3125000000000000000 : ℝ)^256 ≤ (2500134407580913/2500000000000000 : ℝ)^1043 := by
      have hnat : (3125684563927430463 : ℕ)^256*2500000000000000^1043 ≤ 2500134407580913^1043*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125684563927430463 3125000000000000000 2500134407580913 2500000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134407580913/2500000000000000 : ℝ)) (X := (3125684563927430463/3125000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052519885751022143/100000000000000000000 : ℝ) ≤ (10001288823344787/10000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (100052519885751022143/100000000000000000000 : ℝ)^256 ≤ (10001288823344787/10000000000000000 : ℝ)^1043 := by
      have hnat : (100052519885751022143 : ℕ)^256*10000000000000000^1043 ≤ 10001288823344787^1043*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052519885751022143 100000000000000000000 10001288823344787 10000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001288823344787/10000000000000000 : ℝ)) (X := (100052519885751022143/100000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008313372582426947/10000000000000000000 : ℝ) ≤ (5001020008182961/5000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (10008313372582426947/10000000000000000000 : ℝ)^256 ≤ (5001020008182961/5000000000000000 : ℝ)^1043 := by
      have hnat : (10008313372582426947 : ℕ)^256*5000000000000000^1043 ≤ 5001020008182961^1043*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008313372582426947 10000000000000000000 5001020008182961 5000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001020008182961/5000000000000000 : ℝ)) (X := (10008313372582426947/10000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(684563927430463/6250000000000000000 : ℝ) ≤ ((1032154974212047887/1032500000000000000 : ℝ)+2*(150238604227/82600000000000 : ℝ)*(1333/12500 : ℝ))^(1043/256 : ℝ) := by
    rw [show (1032154974212047887/1032500000000000000 : ℝ)+2*(150238604227/82600000000000 : ℝ)*(1333/12500 : ℝ)=(2500134407580913/2500000000000000 : ℝ) by norm_num, show 1+2*(684563927430463/6250000000000000000 : ℝ)=(3125684563927430463/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8313372582426947/20000000000000000000 : ℝ)+(684563927430463/6250000000000000000 : ℝ) ≤ ((1032154974212047887/1032500000000000000 : ℝ)+(150238604227/82600000000000 : ℝ)*((7397/50000 : ℝ)+(1333/12500 : ℝ)))^(1043/256 : ℝ) := by
    rw [show (1032154974212047887/1032500000000000000 : ℝ)+(150238604227/82600000000000 : ℝ)*((7397/50000 : ℝ)+(1333/12500 : ℝ))=(10001288823344787/10000000000000000 : ℝ) by norm_num, show 1+(8313372582426947/20000000000000000000 : ℝ)+(684563927430463/6250000000000000000 : ℝ)=(100052519885751022143/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8313372582426947/20000000000000000000 : ℝ) ≤ ((1032154974212047887/1032500000000000000 : ℝ)+2*(150238604227/82600000000000 : ℝ)*(7397/50000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (1032154974212047887/1032500000000000000 : ℝ)+2*(150238604227/82600000000000 : ℝ)*(7397/50000 : ℝ)=(5001020008182961/5000000000000000 : ℝ) by norm_num, show 1+2*(8313372582426947/20000000000000000000 : ℝ)=(10008313372582426947/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1032154974212047887/1032500000000000000 : ℝ)*(X 1 0+X 2 0)+(150238604227/82600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1333/12500 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (1032154974212047887/1032500000000000000 : ℝ)) (alpha := (150238604227/82600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1032154974212047887/1032500000000000000 : ℝ)*(X 0 1+X 2 1)+(150238604227/82600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1333/12500 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (1032154974212047887/1032500000000000000 : ℝ)) (alpha := (150238604227/82600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1032154974212047887/1032500000000000000 : ℝ)*(X 0 2+X 1 2)+(150238604227/82600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1333/12500 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (1032154974212047887/1032500000000000000 : ℝ)) (alpha := (150238604227/82600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2161342389/10000000000 : ℝ)*X 0 0+(5401420537/10000000000 : ℝ)*X 0 1+(5257838147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346871209/10000000000 : ℝ)*X 1 0+(-89372087/400000000 : ℝ)*X 1 1+(5257838623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673435627/5000000000 : ℝ)*X 2 0+(1314459569/2500000000 : ℝ)*X 2 1+(-1117151287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181408353/5000000000 : ℝ)*X 0 0+(168881543/400000000 : ℝ)*X 0 1+(4508253227/10000000000 : ℝ)*X 0 2+(2181408353/5000000000 : ℝ)*X 1 0+(168881543/400000000 : ℝ)*X 1 1+(4508253227/10000000000 : ℝ)*X 1 2+(2181408353/5000000000 : ℝ)*X 2 0+(168881543/400000000 : ℝ)*X 2 1+(4508253227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-27016869/125000000 : ℝ)*X 0 0+(5258246059/10000000000 : ℝ)*X 0 1+(5401010879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531046933/1000000000 : ℝ)*X 1 0+(-261391223/1250000000 : ℝ)*X 1 1+(675126361/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310469311/10000000000 : ℝ)*X 2 0+(5401011099/10000000000 : ℝ)*X 2 1+(-1045564761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362830671/10000000000 : ℝ)*X 0 0+(563430009/1250000000 : ℝ)*X 0 1+(4222855099/10000000000 : ℝ)*X 0 2+(4362830671/10000000000 : ℝ)*X 1 0+(563430009/1250000000 : ℝ)*X 1 1+(4222855099/10000000000 : ℝ)*X 1 2+(4362830671/10000000000 : ℝ)*X 2 0+(563430009/1250000000 : ℝ)*X 2 1+(4222855099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (567808178008148250310093839/51625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (481736379/100000000000000 : ℝ)*(base19) + (840785073/100000000000000 : ℝ)*(base23) + (26352137/50000000000000 : ℝ)*(lower2) + (67180091/20000000000000 : ℝ)*(upper3) + (213341877/100000000000000 : ℝ)*(lower4) + (2614652101942651/50000000000000 : ℝ)*(major0) + (2614652101942651/50000000000000 : ℝ)*(major1) + (5229304203885303/100000000000000 : ℝ)*(major2) + (696467637291899/10000000000000 : ℝ)*(sp0) + (108823305331769/1562500000000 : ℝ)*(sp1) + (3482345591092261/50000000000000 : ℝ)*(sp2) + (698779230410761/20000000000000 : ℝ)*(sp3) + (3130010121/20000000000000 : ℝ)*(sp4) + (2483265459/12500000000000 : ℝ)*(sp7) + (1746958009088739/50000000000000 : ℝ)*(f.failure) + (1392938404593919/20000000000000 : ℝ)*(f.sum) + (516694125397/1652000000000000000000000000 : ℝ)*base66 + (393433880435640313/51625000000000000000000000000000 : ℝ)*base68 + (1194145555374929761/103250000000000000000000000000000 : ℝ)*base69 + (717776347588890313/51625000000000000000000000000000 : ℝ)*base72 + (1016388427199/1652000000000000000000000000 : ℝ)*base73 + (960071791785179761/103250000000000000000000000000000 : ℝ)*base75 + (1163756521286809063/51625000000000000000000000000000 : ℝ)*base78 + (692268808474065937/51625000000000000000000000000000 : ℝ)*base79 + (4420135972251/1032500000000000000000000000 : ℝ)*base81 + (43395031/2500000000000000000000 : ℝ)*base89 + (43395031/2500000000000000000000 : ℝ)*base91 + (18395031/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (272317322393901877432444467/25812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (954968567/100000000000000 : ℝ)*(base19) + (1468702011/100000000000000 : ℝ)*(base23) + (61950923/20000000000000 : ℝ)*(upper3) + (44024113/25000000000000 : ℝ)*(lower4) + (32067373/50000000000000 : ℝ)*(upper5) + (5259202964729697/100000000000000 : ℝ)*(major0) + (5259202964729697/100000000000000 : ℝ)*(major1) + (5259202964729697/100000000000000 : ℝ)*(major2) + (4740389159/50000000000000 : ℝ)*(sp1) + (39706810413/100000000000000 : ℝ)*(sp2) + (1751128237941417/25000000000000 : ℝ)*(sp4) + (3502251258009391/50000000000000 : ℝ)*(sp5) + (7004471776253243/100000000000000 : ℝ)*(sp6) + (351389262603293/10000000000000 : ℝ)*(sp7) + (351389262603293/10000000000000 : ℝ)*(f.failure) + (1751128237941417/25000000000000 : ℝ)*(f.sum) + (13664093217881/4130000000000000000000000000 : ℝ)*base66 + (1857733172018762261/103250000000000000000000000000000 : ℝ)*base68 + (1279991485346262261/103250000000000000000000000000000 : ℝ)*base70 + (155071353146237739/103250000000000000000000000000000 : ℝ)*base71 + (13474152667641/4130000000000000000000000000 : ℝ)*base74 + (1006293531309762261/103250000000000000000000000000000 : ℝ)*base76 + (657783987751012261/103250000000000000000000000000000 : ℝ)*base78 + (471293166626012261/103250000000000000000000000000000 : ℝ)*base80 + (18817322250159/4130000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (174697/500000000000000000000 : ℝ)*base89 + (174697/500000000000000000000 : ℝ)*base91 + (174697/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1152_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1333/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5597/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1152_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1152_s5_0 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080978393/5000000000 : ℝ)*x 0 + (5394655491/10000000000 : ℝ)*x 1 + (2632099969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080978393/5000000000 : ℝ)^8345 ≤ (13137613537149/100000000000000 : ℝ)^6297 := by
    have hnat : (1080978393 : ℕ)^8345*100000000000000^6297 ≤ 13137613537149^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080978393 5000000000 13137613537149 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394655491/10000000000 : ℝ)^8345 ≤ (22067805256641/50000000000000 : ℝ)^6297 := by
    have hnat : (5394655491 : ℕ)^8345*50000000000000^6297 ≤ 22067805256641^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394655491 10000000000 22067805256641 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632099969/5000000000 : ℝ)^8345 ≤ (10681693982827/25000000000000 : ℝ)^6297 := by
    have hnat : (2632099969 : ℕ)^8345*25000000000000^6297 ≤ 10681693982827^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632099969 5000000000 10681693982827 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080978393/5000000000 : ℝ), (5394655491/10000000000 : ℝ), (2632099969/5000000000 : ℝ)] ![(13137613537149/100000000000000 : ℝ), (22067805256641/50000000000000 : ℝ), (10681693982827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080978393/5000000000 : ℝ)|^8345 ≤ (13137613537149/100000000000000 : ℝ)^6297
        have hw : |(-1080978393/5000000000 : ℝ)|=(1080978393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394655491/10000000000 : ℝ)|^8345 ≤ (22067805256641/50000000000000 : ℝ)^6297
        have hw : |(5394655491/10000000000 : ℝ)|=(5394655491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632099969/5000000000 : ℝ)|^8345 ≤ (10681693982827/25000000000000 : ℝ)^6297
        have hw : |(2632099969/5000000000 : ℝ)|=(2632099969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s5_1 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345173631/10000000000 : ℝ)*x 0 + (-27851869/125000000 : ℝ)*x 1 + (5264199909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345173631/10000000000 : ℝ)^8345 ≤ (8719983872599/20000000000000 : ℝ)^6297 := by
    have hnat : (5345173631 : ℕ)^8345*20000000000000^6297 ≤ 8719983872599^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345173631 10000000000 8719983872599 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27851869/125000000 : ℝ)^8345 ≤ (2734661002443/20000000000000 : ℝ)^6297 := by
    have hnat : (27851869 : ℕ)^8345*20000000000000^6297 ≤ 2734661002443^6297*125000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27851869 125000000 2734661002443 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264199909/10000000000 : ℝ)^8345 ≤ (42726775619377/100000000000000 : ℝ)^6297 := by
    have hnat : (5264199909 : ℕ)^8345*100000000000000^6297 ≤ 42726775619377^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264199909 10000000000 42726775619377 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345173631/10000000000 : ℝ), (-27851869/125000000 : ℝ), (5264199909/10000000000 : ℝ)] ![(8719983872599/20000000000000 : ℝ), (2734661002443/20000000000000 : ℝ), (42726775619377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345173631/10000000000 : ℝ)|^8345 ≤ (8719983872599/20000000000000 : ℝ)^6297
        have hw : |(5345173631/10000000000 : ℝ)|=(5345173631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27851869/125000000 : ℝ)|^8345 ≤ (2734661002443/20000000000000 : ℝ)^6297
        have hw : |(-27851869/125000000 : ℝ)|=(27851869/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264199909/10000000000 : ℝ)|^8345 ≤ (42726775619377/100000000000000 : ℝ)^6297
        have hw : |(5264199909/10000000000 : ℝ)|=(5264199909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s5_2 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345173677/10000000000 : ℝ)*x 0 + (5264199877/10000000000 : ℝ)*x 1 + (-2228149499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345173677/10000000000 : ℝ)^8345 ≤ (8719983972049/20000000000000 : ℝ)^6297 := by
    have hnat : (5345173677 : ℕ)^8345*20000000000000^6297 ≤ 8719983972049^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345173677 10000000000 8719983972049 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264199877/10000000000 : ℝ)^8345 ≤ (21363387637589/50000000000000 : ℝ)^6297 := by
    have hnat : (5264199877 : ℕ)^8345*50000000000000^6297 ≤ 21363387637589^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264199877 10000000000 21363387637589 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2228149499/10000000000 : ℝ)^8345 ≤ (6836652420717/50000000000000 : ℝ)^6297 := by
    have hnat : (2228149499 : ℕ)^8345*50000000000000^6297 ≤ 6836652420717^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228149499 10000000000 6836652420717 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345173677/10000000000 : ℝ), (5264199877/10000000000 : ℝ), (-2228149499/10000000000 : ℝ)] ![(8719983972049/20000000000000 : ℝ), (21363387637589/50000000000000 : ℝ), (6836652420717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345173677/10000000000 : ℝ)|^8345 ≤ (8719983972049/20000000000000 : ℝ)^6297
        have hw : |(5345173677/10000000000 : ℝ)|=(5345173677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264199877/10000000000 : ℝ)|^8345 ≤ (21363387637589/50000000000000 : ℝ)^6297
        have hw : |(5264199877/10000000000 : ℝ)|=(5264199877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2228149499/10000000000 : ℝ)|^8345 ≤ (6836652420717/50000000000000 : ℝ)^6297
        have hw : |(-2228149499/10000000000 : ℝ)|=(2228149499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s5_3 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363176093/10000000000 : ℝ)*x 0 + (4235075741/10000000000 : ℝ)*x 1 + (4495123027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363176093/10000000000 : ℝ)^8345 ≤ (33316107883323/100000000000000 : ℝ)^6297 := by
    have hnat : (4363176093 : ℕ)^8345*100000000000000^6297 ≤ 33316107883323^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363176093 10000000000 33316107883323 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235075741/10000000000 : ℝ)^8345 ≤ (1601303550787/5000000000000 : ℝ)^6297 := by
    have hnat : (4235075741 : ℕ)^8345*5000000000000^6297 ≤ 1601303550787^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235075741 10000000000 1601303550787 5000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495123027/10000000000 : ℝ)^8345 ≤ (17328910542763/50000000000000 : ℝ)^6297 := by
    have hnat : (4495123027 : ℕ)^8345*50000000000000^6297 ≤ 17328910542763^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495123027 10000000000 17328910542763 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363176093/10000000000 : ℝ), (4235075741/10000000000 : ℝ), (4495123027/10000000000 : ℝ)] ![(33316107883323/100000000000000 : ℝ), (1601303550787/5000000000000 : ℝ), (17328910542763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363176093/10000000000 : ℝ)|^8345 ≤ (33316107883323/100000000000000 : ℝ)^6297
        have hw : |(4363176093/10000000000 : ℝ)|=(4363176093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235075741/10000000000 : ℝ)|^8345 ≤ (1601303550787/5000000000000 : ℝ)^6297
        have hw : |(4235075741/10000000000 : ℝ)|=(4235075741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495123027/10000000000 : ℝ)|^8345 ≤ (17328910542763/50000000000000 : ℝ)^6297
        have hw : |(4495123027/10000000000 : ℝ)|=(4495123027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s5_4 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-270245221/1250000000 : ℝ)*x 0 + (5264537283/10000000000 : ℝ)*x 1 + (1078863423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270245221/1250000000 : ℝ)^8345 ≤ (6568826828809/50000000000000 : ℝ)^6297 := by
    have hnat : (270245221 : ℕ)^8345*50000000000000^6297 ≤ 6568826828809^6297*1250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270245221 1250000000 6568826828809 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264537283/10000000000 : ℝ)^8345 ≤ (21365202266081/50000000000000 : ℝ)^6297 := by
    have hnat : (5264537283 : ℕ)^8345*50000000000000^6297 ≤ 21365202266081^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264537283 10000000000 21365202266081 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078863423/2000000000 : ℝ)^8345 ≤ (44131941804891/100000000000000 : ℝ)^6297 := by
    have hnat : (1078863423 : ℕ)^8345*100000000000000^6297 ≤ 44131941804891^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078863423 2000000000 44131941804891 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270245221/1250000000 : ℝ), (5264537283/10000000000 : ℝ), (1078863423/2000000000 : ℝ)] ![(6568826828809/50000000000000 : ℝ), (21365202266081/50000000000000 : ℝ), (44131941804891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270245221/1250000000 : ℝ)|^8345 ≤ (6568826828809/50000000000000 : ℝ)^6297
        have hw : |(-270245221/1250000000 : ℝ)|=(270245221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264537283/10000000000 : ℝ)|^8345 ≤ (21365202266081/50000000000000 : ℝ)^6297
        have hw : |(5264537283/10000000000 : ℝ)|=(5264537283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078863423/2000000000 : ℝ)|^8345 ≤ (44131941804891/100000000000000 : ℝ)^6297
        have hw : |(1078863423/2000000000 : ℝ)|=(1078863423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s5_5 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312098677/10000000000 : ℝ)*x 0 + (-2098031451/10000000000 : ℝ)*x 1 + (5394317273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312098677/10000000000 : ℝ)^8345 ≤ (21621373466569/50000000000000 : ℝ)^6297 := by
    have hnat : (5312098677 : ℕ)^8345*50000000000000^6297 ≤ 21621373466569^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312098677 10000000000 21621373466569 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2098031451/10000000000 : ℝ)^8345 ≤ (12625309539367/100000000000000 : ℝ)^6297 := by
    have hnat : (2098031451 : ℕ)^8345*100000000000000^6297 ≤ 12625309539367^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098031451 10000000000 12625309539367 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394317273/10000000000 : ℝ)^8345 ≤ (22065971758963/50000000000000 : ℝ)^6297 := by
    have hnat : (5394317273 : ℕ)^8345*50000000000000^6297 ≤ 22065971758963^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394317273 10000000000 22065971758963 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312098677/10000000000 : ℝ), (-2098031451/10000000000 : ℝ), (5394317273/10000000000 : ℝ)] ![(21621373466569/50000000000000 : ℝ), (12625309539367/100000000000000 : ℝ), (22065971758963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312098677/10000000000 : ℝ)|^8345 ≤ (21621373466569/50000000000000 : ℝ)^6297
        have hw : |(5312098677/10000000000 : ℝ)|=(5312098677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2098031451/10000000000 : ℝ)|^8345 ≤ (12625309539367/100000000000000 : ℝ)^6297
        have hw : |(-2098031451/10000000000 : ℝ)|=(2098031451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394317273/10000000000 : ℝ)|^8345 ≤ (22065971758963/50000000000000 : ℝ)^6297
        have hw : |(5394317273/10000000000 : ℝ)|=(5394317273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s5_6 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656049057/5000000000 : ℝ)*x 0 + (5394317687/10000000000 : ℝ)*x 1 + (-41960633/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656049057/5000000000 : ℝ)^8345 ≤ (4324274085951/10000000000000 : ℝ)^6297 := by
    have hnat : (2656049057 : ℕ)^8345*10000000000000^6297 ≤ 4324274085951^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656049057 5000000000 4324274085951 10000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394317687/10000000000 : ℝ)^8345 ≤ (2758246750407/6250000000000 : ℝ)^6297 := by
    have hnat : (5394317687 : ℕ)^8345*6250000000000^6297 ≤ 2758246750407^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394317687 10000000000 2758246750407 6250000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41960633/200000000 : ℝ)^8345 ≤ (12625311126363/100000000000000 : ℝ)^6297 := by
    have hnat : (41960633 : ℕ)^8345*100000000000000^6297 ≤ 12625311126363^6297*200000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41960633 200000000 12625311126363 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656049057/5000000000 : ℝ), (5394317687/10000000000 : ℝ), (-41960633/200000000 : ℝ)] ![(4324274085951/10000000000000 : ℝ), (2758246750407/6250000000000 : ℝ), (12625311126363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656049057/5000000000 : ℝ)|^8345 ≤ (4324274085951/10000000000000 : ℝ)^6297
        have hw : |(2656049057/5000000000 : ℝ)|=(2656049057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394317687/10000000000 : ℝ)|^8345 ≤ (2758246750407/6250000000000 : ℝ)^6297
        have hw : |(5394317687/10000000000 : ℝ)|=(5394317687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41960633/200000000 : ℝ)|^8345 ≤ (12625311126363/100000000000000 : ℝ)^6297
        have hw : |(-41960633/200000000 : ℝ)|=(41960633/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s5_7 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136349591/312500000 : ℝ)*x 0 + (898890231/2000000000 : ℝ)*x 1 + (4235749803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136349591/312500000 : ℝ)^8345 ≤ (6663243472497/20000000000000 : ℝ)^6297 := by
    have hnat : (136349591 : ℕ)^8345*20000000000000^6297 ≤ 6663243472497^6297*312500000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136349591 312500000 6663243472497 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898890231/2000000000 : ℝ)^8345 ≤ (34650956278923/100000000000000 : ℝ)^6297 := by
    have hnat : (898890231 : ℕ)^8345*100000000000000^6297 ≤ 34650956278923^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898890231 2000000000 34650956278923 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4235749803/10000000000 : ℝ)^8345 ≤ (32032826340197/100000000000000 : ℝ)^6297 := by
    have hnat : (4235749803 : ℕ)^8345*100000000000000^6297 ≤ 32032826340197^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235749803 10000000000 32032826340197 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136349591/312500000 : ℝ), (898890231/2000000000 : ℝ), (4235749803/10000000000 : ℝ)] ![(6663243472497/20000000000000 : ℝ), (34650956278923/100000000000000 : ℝ), (32032826340197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136349591/312500000 : ℝ)|^8345 ≤ (6663243472497/20000000000000 : ℝ)^6297
        have hw : |(136349591/312500000 : ℝ)|=(136349591/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898890231/2000000000 : ℝ)|^8345 ≤ (34650956278923/100000000000000 : ℝ)^6297
        have hw : |(898890231/2000000000 : ℝ)|=(898890231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4235749803/10000000000 : ℝ)|^8345 ≤ (32032826340197/100000000000000 : ℝ)^6297
        have hw : |(4235749803/10000000000 : ℝ)|=(4235749803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1152_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5597/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1133/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14093/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5597/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5597/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5597/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5597/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5597/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5597/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5597/50000 : ℝ) ^ (1043/256 : ℝ) ≤ (13346214121026419/100000000000000000000 : ℝ) := by
    have hpowers : (5597/50000 : ℝ)^1043 ≤ (13346214121026419/100000000000000000000 : ℝ)^256 := by
      have hnat : (5597 : ℕ)^1043*100000000000000000000^256 ≤ 13346214121026419^256*50000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5597 50000 13346214121026419 100000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5597/50000 : ℝ)) (X := (13346214121026419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (1043/256 : ℝ) ≤ (35529830511167623/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^1043 ≤ (35529830511167623/100000000000000000000 : ℝ)^256 := by
      have hnat : (2847 : ℕ)^1043*100000000000000000000^256 ≤ 35529830511167623^256*20000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 35529830511167623 100000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (35529830511167623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013346214121026419/50000000000000000000 : ℝ) ≤ (5000327544276019/5000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50013346214121026419/50000000000000000000 : ℝ)^256 ≤ (5000327544276019/5000000000000000 : ℝ)^1043 := by
      have hnat : (50013346214121026419 : ℕ)^256*5000000000000000^1043 ≤ 5000327544276019^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013346214121026419 50000000000000000000 5000327544276019 5000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000327544276019/5000000000000000 : ℝ)) (X := (50013346214121026419/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024438022316097021/50000000000000000000 : ℝ) ≤ (10001199420982417/10000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50024438022316097021/50000000000000000000 : ℝ)^256 ≤ (10001199420982417/10000000000000000 : ℝ)^1043 := by
      have hnat : (50024438022316097021 : ℕ)^256*10000000000000000^1043 ≤ 10001199420982417^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024438022316097021 50000000000000000000 10001199420982417 10000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001199420982417/10000000000000000 : ℝ)) (X := (50024438022316097021/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035529830511167623/50000000000000000000 : ℝ) ≤ (2500435938353199/2500000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50035529830511167623/50000000000000000000 : ℝ)^256 ≤ (2500435938353199/2500000000000000 : ℝ)^1043 := by
      have hnat : (50035529830511167623 : ℕ)^256*2500000000000000^1043 ≤ 2500435938353199^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035529830511167623 50000000000000000000 2500435938353199 2500000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500435938353199/2500000000000000 : ℝ)) (X := (50035529830511167623/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13346214121026419/100000000000000000000 : ℝ) ≤ ((15199902804917711253/15205000000000000000 : ℝ)+2*(544332430379/304100000000000 : ℝ)*(5597/50000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (15199902804917711253/15205000000000000000 : ℝ)+2*(544332430379/304100000000000 : ℝ)*(5597/50000 : ℝ)=(5000327544276019/5000000000000000 : ℝ) by norm_num, show 1+2*(13346214121026419/100000000000000000000 : ℝ)=(50013346214121026419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35529830511167623/100000000000000000000 : ℝ)+(13346214121026419/100000000000000000000 : ℝ) ≤ ((15199902804917711253/15205000000000000000 : ℝ)+(544332430379/304100000000000 : ℝ)*((2847/20000 : ℝ)+(5597/50000 : ℝ)))^(1043/256 : ℝ) := by
    rw [show (15199902804917711253/15205000000000000000 : ℝ)+(544332430379/304100000000000 : ℝ)*((2847/20000 : ℝ)+(5597/50000 : ℝ))=(10001199420982417/10000000000000000 : ℝ) by norm_num, show 1+(35529830511167623/100000000000000000000 : ℝ)+(13346214121026419/100000000000000000000 : ℝ)=(50024438022316097021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35529830511167623/100000000000000000000 : ℝ) ≤ ((15199902804917711253/15205000000000000000 : ℝ)+2*(544332430379/304100000000000 : ℝ)*(2847/20000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (15199902804917711253/15205000000000000000 : ℝ)+2*(544332430379/304100000000000 : ℝ)*(2847/20000 : ℝ)=(2500435938353199/2500000000000000 : ℝ) by norm_num, show 1+2*(35529830511167623/100000000000000000000 : ℝ)=(50035529830511167623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15199902804917711253/15205000000000000000 : ℝ)*(X 1 0+X 2 0)+(544332430379/304100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (5597/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15199902804917711253/15205000000000000000 : ℝ)) (alpha := (544332430379/304100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15199902804917711253/15205000000000000000 : ℝ)*(X 0 1+X 2 1)+(544332430379/304100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (5597/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15199902804917711253/15205000000000000000 : ℝ)) (alpha := (544332430379/304100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15199902804917711253/15205000000000000000 : ℝ)*(X 0 2+X 1 2)+(544332430379/304100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (5597/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15199902804917711253/15205000000000000000 : ℝ)) (alpha := (544332430379/304100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1080978393/5000000000 : ℝ)*X 0 0+(5394655491/10000000000 : ℝ)*X 0 1+(2632099969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345173631/10000000000 : ℝ)*X 1 0+(-27851869/125000000 : ℝ)*X 1 1+(5264199909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345173677/10000000000 : ℝ)*X 2 0+(5264199877/10000000000 : ℝ)*X 2 1+(-2228149499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363176093/10000000000 : ℝ)*X 0 0+(4235075741/10000000000 : ℝ)*X 0 1+(4495123027/10000000000 : ℝ)*X 0 2+(4363176093/10000000000 : ℝ)*X 1 0+(4235075741/10000000000 : ℝ)*X 1 1+(4495123027/10000000000 : ℝ)*X 1 2+(4363176093/10000000000 : ℝ)*X 2 0+(4235075741/10000000000 : ℝ)*X 2 1+(4495123027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-270245221/1250000000 : ℝ)*X 0 0+(5264537283/10000000000 : ℝ)*X 0 1+(1078863423/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312098677/10000000000 : ℝ)*X 1 0+(-2098031451/10000000000 : ℝ)*X 1 1+(5394317273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656049057/5000000000 : ℝ)*X 2 0+(5394317687/10000000000 : ℝ)*X 2 1+(-41960633/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136349591/312500000 : ℝ)*X 0 0+(898890231/2000000000 : ℝ)*X 0 1+(4235749803/10000000000 : ℝ)*X 0 2+(136349591/312500000 : ℝ)*X 1 0+(898890231/2000000000 : ℝ)*X 1 1+(4235749803/10000000000 : ℝ)*X 1 2+(136349591/312500000 : ℝ)*X 2 0+(898890231/2000000000 : ℝ)*X 2 1+(4235749803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1799814498823339315798549899/380125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24097619/4000000000000 : ℝ)*(base19) + (298546793/50000000000000 : ℝ)*(base23) + (38119173/100000000000000 : ℝ)*(lower2) + (84307327/100000000000000 : ℝ)*(upper3) + (15021903/20000000000000 : ℝ)*(upper5) + (5755471147281539/100000000000000 : ℝ)*(major0) + (5755471147281539/100000000000000 : ℝ)*(major1) + (287773557364077/5000000000000 : ℝ)*(major2) + (7665458321978767/100000000000000 : ℝ)*(sp0) + (1916367864607317/25000000000000 : ℝ)*(sp1) + (7665471463776157/100000000000000 : ℝ)*(sp2) + (480682723899251/12500000000000 : ℝ)*(sp3) + (13738890977/100000000000000 : ℝ)*(sp4) + (8284672769/100000000000000 : ℝ)*(sp7) + (1922735037933389/50000000000000 : ℝ)*(f.failure) + (7665472060869743/100000000000000 : ℝ)*(f.sum) + (130467104008601/30410000000000000000000000000 : ℝ)*base65 + (5199524002556958367/1520500000000000000000000000000000 : ℝ)*base67 + (1121182398273039019/76025000000000000000000000000000 : ℝ)*base70 + (20025358485192458367/1520500000000000000000000000000000 : ℝ)*base71 + (178819402714111/30410000000000000000000000000 : ℝ)*base73 + (227527800870685981/76025000000000000000000000000000 : ℝ)*base75 + (8709361154963008367/1520500000000000000000000000000000 : ℝ)*base77 + (22256375338717508367/1520500000000000000000000000000000 : ℝ)*base79 + (14901683209619/15205000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (30849881/2500000000000000000000 : ℝ)*base89 + (30849881/2500000000000000000000 : ℝ)*base91 + (5849881/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4293597725594825315590983501/760250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101294373/6250000000000 : ℝ)*(base19) + (1574904933/100000000000000 : ℝ)*(base23) + (90639783/100000000000000 : ℝ)*(upper3) + (387961067/100000000000000 : ℝ)*(lower4) + (5785400785449139/100000000000000 : ℝ)*(major0) + (5785400785449139/100000000000000 : ℝ)*(major1) + (5785400785449139/100000000000000 : ℝ)*(major2) + (119515499/200000000000 : ℝ)*(sp1) + (4141379731/6250000000000 : ℝ)*(sp2) + (1537190313/25000000000000 : ℝ)*(sp3) + (770533406849613/10000000000000 : ℝ)*(sp4) + (3852636345018331/50000000000000 : ℝ)*(sp5) + (3852633115757751/50000000000000 : ℝ)*(sp6) + (1932730582693559/50000000000000 : ℝ)*(sp7) + (386546731414837/10000000000000 : ℝ)*(f.failure) + (770533406849613/10000000000000 : ℝ)*(f.sum) + (63654359179779/15205000000000000000000000000 : ℝ)*base66 + (11215246963057511167/1520500000000000000000000000000000 : ℝ)*base67 + (13962604119210488833/1520500000000000000000000000000000 : ℝ)*base70 + (4701886683679488833/1520500000000000000000000000000000 : ℝ)*base72 + (25531200960619/15205000000000000000000000000 : ℝ)*base74 + (35864484095368488833/1520500000000000000000000000000000 : ℝ)*base76 + (9618962719027511167/1520500000000000000000000000000000 : ℝ)*base77 + (12770577399700488833/1520500000000000000000000000000000 : ℝ)*base80 + (76236234271889/15205000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5976927/500000000000000000000 : ℝ)*base90 + (5976927/500000000000000000000 : ℝ)*base92 + (5976927/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1152_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5597/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1152_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1152_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1823/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1152_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1152_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1152_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1823/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1152_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
