-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1160_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:39:30.994978+00:00
-- url     : https://prove2.me/submissions/d0d5c093-7a11-4184-ac0c-75185aa3d4b9

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
theorem support_rectangle_w1160_s0_0 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-943063419/5000000000 : ℝ)*x 0 + (6050179301/10000000000 : ℝ)*x 1 + (1195686131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943063419/5000000000 : ℝ)^8353 ≤ (5485682900653/50000000000000 : ℝ)^6305 := by
    have hnat : (943063419 : ℕ)^8353*50000000000000^6305 ≤ 5485682900653^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943063419 5000000000 5485682900653 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6050179301/10000000000 : ℝ)^8353 ≤ (12847596042147/25000000000000 : ℝ)^6305 := by
    have hnat : (6050179301 : ℕ)^8353*25000000000000^6305 ≤ 12847596042147^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6050179301 10000000000 12847596042147 25000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195686131/2500000000 : ℝ)^8353 ≤ (37638250017517/100000000000000 : ℝ)^6305 := by
    have hnat : (1195686131 : ℕ)^8353*100000000000000^6305 ≤ 37638250017517^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195686131 2500000000 37638250017517 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-943063419/5000000000 : ℝ), (6050179301/10000000000 : ℝ), (1195686131/2500000000 : ℝ)] ![(5485682900653/50000000000000 : ℝ), (12847596042147/25000000000000 : ℝ), (37638250017517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-943063419/5000000000 : ℝ)|^8353 ≤ (5485682900653/50000000000000 : ℝ)^6305
        have hw : |(-943063419/5000000000 : ℝ)|=(943063419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6050179301/10000000000 : ℝ)|^8353 ≤ (12847596042147/25000000000000 : ℝ)^6305
        have hw : |(6050179301/10000000000 : ℝ)|=(6050179301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1195686131/2500000000 : ℝ)|^8353 ≤ (37638250017517/100000000000000 : ℝ)^6305
        have hw : |(1195686131/2500000000 : ℝ)|=(1195686131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s0_1 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757889801/5000000000 : ℝ)*x 0 + (-2612975863/10000000000 : ℝ)*x 1 + (191309781/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757889801/5000000000 : ℝ)^8353 ≤ (45464796696271/100000000000000 : ℝ)^6305 := by
    have hnat : (2757889801 : ℕ)^8353*100000000000000^6305 ≤ 45464796696271^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757889801 5000000000 45464796696271 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612975863/10000000000 : ℝ)^8353 ≤ (8448476630951/50000000000000 : ℝ)^6305 := by
    have hnat : (2612975863 : ℕ)^8353*50000000000000^6305 ≤ 8448476630951^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612975863 10000000000 8448476630951 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191309781/400000000 : ℝ)^8353 ≤ (37638250027943/100000000000000 : ℝ)^6305 := by
    have hnat : (191309781 : ℕ)^8353*100000000000000^6305 ≤ 37638250027943^6305*400000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191309781 400000000 37638250027943 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757889801/5000000000 : ℝ), (-2612975863/10000000000 : ℝ), (191309781/400000000 : ℝ)] ![(45464796696271/100000000000000 : ℝ), (8448476630951/50000000000000 : ℝ), (37638250027943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757889801/5000000000 : ℝ)|^8353 ≤ (45464796696271/100000000000000 : ℝ)^6305
        have hw : |(2757889801/5000000000 : ℝ)|=(2757889801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2612975863/10000000000 : ℝ)|^8353 ≤ (8448476630951/50000000000000 : ℝ)^6305
        have hw : |(-2612975863/10000000000 : ℝ)|=(2612975863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(191309781/400000000 : ℝ)|^8353 ≤ (37638250027943/100000000000000 : ℝ)^6305
        have hw : |(191309781/400000000 : ℝ)|=(191309781/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s0_2 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1378944901/2500000000 : ℝ)*x 0 + (4782744521/10000000000 : ℝ)*x 1 + (-326621983/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378944901/2500000000 : ℝ)^8353 ≤ (45464796718111/100000000000000 : ℝ)^6305 := by
    have hnat : (1378944901 : ℕ)^8353*100000000000000^6305 ≤ 45464796718111^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378944901 2500000000 45464796718111 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4782744521/10000000000 : ℝ)^8353 ≤ (117619531207/312500000000 : ℝ)^6305 := by
    have hnat : (4782744521 : ℕ)^8353*312500000000^6305 ≤ 117619531207^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782744521 10000000000 117619531207 312500000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326621983/1250000000 : ℝ)^8353 ≤ (16896953270469/100000000000000 : ℝ)^6305 := by
    have hnat : (326621983 : ℕ)^8353*100000000000000^6305 ≤ 16896953270469^6305*1250000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326621983 1250000000 16896953270469 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378944901/2500000000 : ℝ), (4782744521/10000000000 : ℝ), (-326621983/1250000000 : ℝ)] ![(45464796718111/100000000000000 : ℝ), (117619531207/312500000000 : ℝ), (16896953270469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378944901/2500000000 : ℝ)|^8353 ≤ (45464796718111/100000000000000 : ℝ)^6305
        have hw : |(1378944901/2500000000 : ℝ)|=(1378944901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4782744521/10000000000 : ℝ)|^8353 ≤ (117619531207/312500000000 : ℝ)^6305
        have hw : |(4782744521/10000000000 : ℝ)|=(4782744521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-326621983/1250000000 : ℝ)|^8353 ≤ (16896953270469/100000000000000 : ℝ)^6305
        have hw : |(-326621983/1250000000 : ℝ)|=(326621983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s0_3 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2099769457/5000000000 : ℝ)*x 0 + (624051827/2000000000 : ℝ)*x 1 + (5650693439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099769457/5000000000 : ℝ)^8353 ≤ (15840882387829/50000000000000 : ℝ)^6305 := by
    have hnat : (2099769457 : ℕ)^8353*50000000000000^6305 ≤ 15840882387829^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099769457 5000000000 15840882387829 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624051827/2000000000 : ℝ)^8353 ≤ (10687174108837/50000000000000 : ℝ)^6305 := by
    have hnat : (624051827 : ℕ)^8353*50000000000000^6305 ≤ 10687174108837^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624051827 2000000000 10687174108837 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5650693439/10000000000 : ℝ)^8353 ≤ (9388777399067/20000000000000 : ℝ)^6305 := by
    have hnat : (5650693439 : ℕ)^8353*20000000000000^6305 ≤ 9388777399067^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5650693439 10000000000 9388777399067 20000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099769457/5000000000 : ℝ), (624051827/2000000000 : ℝ), (5650693439/10000000000 : ℝ)] ![(15840882387829/50000000000000 : ℝ), (10687174108837/50000000000000 : ℝ), (9388777399067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099769457/5000000000 : ℝ)|^8353 ≤ (15840882387829/50000000000000 : ℝ)^6305
        have hw : |(2099769457/5000000000 : ℝ)|=(2099769457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624051827/2000000000 : ℝ)|^8353 ≤ (10687174108837/50000000000000 : ℝ)^6305
        have hw : |(624051827/2000000000 : ℝ)|=(624051827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5650693439/10000000000 : ℝ)|^8353 ≤ (9388777399067/20000000000000 : ℝ)^6305
        have hw : |(5650693439/10000000000 : ℝ)|=(5650693439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s0_4 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-378243933/2000000000 : ℝ)*x 0 + (4815431579/10000000000 : ℝ)*x 1 + (1203268337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (378243933/2000000000 : ℝ)^8353 ≤ (5505314985147/50000000000000 : ℝ)^6305 := by
    have hnat : (378243933 : ℕ)^8353*50000000000000^6305 ≤ 5505314985147^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378243933 2000000000 5505314985147 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4815431579/10000000000 : ℝ)^8353 ≤ (37979416591581/100000000000000 : ℝ)^6305 := by
    have hnat : (4815431579 : ℕ)^8353*100000000000000^6305 ≤ 37979416591581^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815431579 10000000000 37979416591581 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203268337/2000000000 : ℝ)^8353 ≤ (10201990685321/20000000000000 : ℝ)^6305 := by
    have hnat : (1203268337 : ℕ)^8353*20000000000000^6305 ≤ 10201990685321^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203268337 2000000000 10201990685321 20000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-378243933/2000000000 : ℝ), (4815431579/10000000000 : ℝ), (1203268337/2000000000 : ℝ)] ![(5505314985147/50000000000000 : ℝ), (37979416591581/100000000000000 : ℝ), (10201990685321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-378243933/2000000000 : ℝ)|^8353 ≤ (5505314985147/50000000000000 : ℝ)^6305
        have hw : |(-378243933/2000000000 : ℝ)|=(378243933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4815431579/10000000000 : ℝ)|^8353 ≤ (37979416591581/100000000000000 : ℝ)^6305
        have hw : |(4815431579/10000000000 : ℝ)|=(4815431579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203268337/2000000000 : ℝ)|^8353 ≤ (10201990685321/20000000000000 : ℝ)^6305
        have hw : |(1203268337/2000000000 : ℝ)|=(1203268337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s0_5 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171302033/10000000000 : ℝ)*x 0 + (-275875773/2000000000 : ℝ)*x 1 + (3008170743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171302033/10000000000 : ℝ)^8353 ≤ (41741780958963/100000000000000 : ℝ)^6305 := by
    have hnat : (5171302033 : ℕ)^8353*100000000000000^6305 ≤ 41741780958963^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171302033 10000000000 41741780958963 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275875773/2000000000 : ℝ)^8353 ≤ (906033479513/12500000000000 : ℝ)^6305 := by
    have hnat : (275875773 : ℕ)^8353*12500000000000^6305 ≤ 906033479513^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275875773 2000000000 906033479513 12500000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3008170743/5000000000 : ℝ)^8353 ≤ (1275248779783/2500000000000 : ℝ)^6305 := by
    have hnat : (3008170743 : ℕ)^8353*2500000000000^6305 ≤ 1275248779783^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008170743 5000000000 1275248779783 2500000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171302033/10000000000 : ℝ), (-275875773/2000000000 : ℝ), (3008170743/5000000000 : ℝ)] ![(41741780958963/100000000000000 : ℝ), (906033479513/12500000000000 : ℝ), (1275248779783/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171302033/10000000000 : ℝ)|^8353 ≤ (41741780958963/100000000000000 : ℝ)^6305
        have hw : |(5171302033/10000000000 : ℝ)|=(5171302033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275875773/2000000000 : ℝ)|^8353 ≤ (906033479513/12500000000000 : ℝ)^6305
        have hw : |(-275875773/2000000000 : ℝ)|=(275875773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3008170743/5000000000 : ℝ)|^8353 ≤ (1275248779783/2500000000000 : ℝ)^6305
        have hw : |(3008170743/5000000000 : ℝ)|=(3008170743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s0_6 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171302007/10000000000 : ℝ)*x 0 + (150408539/250000000 : ℝ)*x 1 + (-275875757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171302007/10000000000 : ℝ)^8353 ≤ (20870890340463/50000000000000 : ℝ)^6305 := by
    have hnat : (5171302007 : ℕ)^8353*50000000000000^6305 ≤ 20870890340463^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171302007 10000000000 20870890340463 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150408539/250000000 : ℝ)^8353 ≤ (12752488005633/25000000000000 : ℝ)^6305 := by
    have hnat : (150408539 : ℕ)^8353*25000000000000^6305 ≤ 12752488005633^6305*250000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150408539 250000000 12752488005633 25000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275875757/2000000000 : ℝ)^8353 ≤ (7248267279177/100000000000000 : ℝ)^6305 := by
    have hnat : (275875757 : ℕ)^8353*100000000000000^6305 ≤ 7248267279177^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275875757 2000000000 7248267279177 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171302007/10000000000 : ℝ), (150408539/250000000 : ℝ), (-275875757/2000000000 : ℝ)] ![(20870890340463/50000000000000 : ℝ), (12752488005633/25000000000000 : ℝ), (7248267279177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171302007/10000000000 : ℝ)|^8353 ≤ (20870890340463/50000000000000 : ℝ)^6305
        have hw : |(5171302007/10000000000 : ℝ)|=(5171302007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(150408539/250000000 : ℝ)|^8353 ≤ (12752488005633/25000000000000 : ℝ)^6305
        have hw : |(150408539/250000000 : ℝ)|=(150408539/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275875757/2000000000 : ℝ)|^8353 ≤ (7248267279177/100000000000000 : ℝ)^6305
        have hw : |(-275875757/2000000000 : ℝ)|=(275875757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s0_7 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (168388277/400000000 : ℝ)*x 0 + (349089591/625000000 : ℝ)*x 1 + (637563239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168388277/400000000 : ℝ)^8353 ≤ (1271337194213/4000000000000 : ℝ)^6305 := by
    have hnat : (168388277 : ℕ)^8353*4000000000000^6305 ≤ 1271337194213^6305*400000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168388277 400000000 1271337194213 4000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349089591/625000000 : ℝ)^8353 ≤ (23113488900369/50000000000000 : ℝ)^6305 := by
    have hnat : (349089591 : ℕ)^8353*50000000000000^6305 ≤ 23113488900369^6305*625000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349089591 625000000 23113488900369 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637563239/2000000000 : ℝ)^8353 ≤ (10994796162371/50000000000000 : ℝ)^6305 := by
    have hnat : (637563239 : ℕ)^8353*50000000000000^6305 ≤ 10994796162371^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637563239 2000000000 10994796162371 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168388277/400000000 : ℝ), (349089591/625000000 : ℝ), (637563239/2000000000 : ℝ)] ![(1271337194213/4000000000000 : ℝ), (23113488900369/50000000000000 : ℝ), (10994796162371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168388277/400000000 : ℝ)|^8353 ≤ (1271337194213/4000000000000 : ℝ)^6305
        have hw : |(168388277/400000000 : ℝ)|=(168388277/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(349089591/625000000 : ℝ)|^8353 ≤ (23113488900369/50000000000000 : ℝ)^6305
        have hw : |(349089591/625000000 : ℝ)|=(349089591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637563239/2000000000 : ℝ)|^8353 ≤ (10994796162371/50000000000000 : ℝ)^6305
        have hw : |(637563239/2000000000 : ℝ)|=(637563239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1160_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (487/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13873/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (261/64 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^261 ≤ (0 : ℝ)^64 := by
      have hnat : (0 : ℕ)^261*1^64 ≤ 0^64*1^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (261/64 : ℝ) ≤ (2383147385832806983/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^261 ≤ (2383147385832806983/100000000000000000000 : ℝ)^64 := by
      have hnat : (2 : ℕ)^261*100000000000000000000^64 ≤ 2383147385832806983^64*5^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2383147385832806983 100000000000000000000 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2383147385832806983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (1 : ℝ)^64 ≤ (1 : ℝ)^261 := by
      have hnat : (1 : ℕ)^64*1^261 ≤ 1^261*1^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (102383147385832806983/100000000000000000000 : ℝ) ≤ (5028959480519509/5000000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (102383147385832806983/100000000000000000000 : ℝ)^64 ≤ (5028959480519509/5000000000000000 : ℝ)^261 := by
      have hnat : (102383147385832806983 : ℕ)^64*5000000000000000^261 ≤ 5028959480519509^261*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102383147385832806983 100000000000000000000 5028959480519509 5000000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028959480519509/5000000000000000 : ℝ)) (X := (102383147385832806983/100000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (52383147385832806983/50000000000000000000 : ℝ) ≤ (2528959480519509/2500000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (52383147385832806983/50000000000000000000 : ℝ)^64 ≤ (2528959480519509/2500000000000000 : ℝ)^261 := by
      have hnat : (52383147385832806983 : ℕ)^64*2500000000000000^261 ≤ 2528959480519509^261*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52383147385832806983 50000000000000000000 2528959480519509 2500000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528959480519509/2500000000000000 : ℝ)) (X := (52383147385832806983/50000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28959480519509/2000000000000000 : ℝ)*(0 : ℝ))^(261/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(28959480519509/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2383147385832806983/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28959480519509/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(261/64 : ℝ) := by
    rw [show (1 : ℝ)+(28959480519509/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028959480519509/5000000000000000 : ℝ) by norm_num, show 1+(2383147385832806983/100000000000000000000 : ℝ)+(0 : ℝ)=(102383147385832806983/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2383147385832806983/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28959480519509/2000000000000000 : ℝ)*(2/5 : ℝ))^(261/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(28959480519509/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528959480519509/2500000000000000 : ℝ) by norm_num, show 1+2*(2383147385832806983/100000000000000000000 : ℝ)=(52383147385832806983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28959480519509/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28959480519509/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28959480519509/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28959480519509/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28959480519509/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28959480519509/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-943063419/5000000000 : ℝ)*X 0 0+(6050179301/10000000000 : ℝ)*X 0 1+(1195686131/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2757889801/5000000000 : ℝ)*X 1 0+(-2612975863/10000000000 : ℝ)*X 1 1+(191309781/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378944901/2500000000 : ℝ)*X 2 0+(4782744521/10000000000 : ℝ)*X 2 1+(-326621983/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2099769457/5000000000 : ℝ)*X 0 0+(624051827/2000000000 : ℝ)*X 0 1+(5650693439/10000000000 : ℝ)*X 0 2+(2099769457/5000000000 : ℝ)*X 1 0+(624051827/2000000000 : ℝ)*X 1 1+(5650693439/10000000000 : ℝ)*X 1 2+(2099769457/5000000000 : ℝ)*X 2 0+(624051827/2000000000 : ℝ)*X 2 1+(5650693439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-378243933/2000000000 : ℝ)*X 0 0+(4815431579/10000000000 : ℝ)*X 0 1+(1203268337/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171302033/10000000000 : ℝ)*X 1 0+(-275875773/2000000000 : ℝ)*X 1 1+(3008170743/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5171302007/10000000000 : ℝ)*X 2 0+(150408539/250000000 : ℝ)*X 2 1+(-275875757/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((168388277/400000000 : ℝ)*X 0 0+(349089591/625000000 : ℝ)*X 0 1+(637563239/2000000000 : ℝ)*X 0 2+(168388277/400000000 : ℝ)*X 1 0+(349089591/625000000 : ℝ)*X 1 1+(637563239/2000000000 : ℝ)*X 1 2+(168388277/400000000 : ℝ)*X 2 0+(349089591/625000000 : ℝ)*X 2 1+(637563239/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (170791658254222017259107/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72792417/100000000000000 : ℝ)*(base1) + (1684706773/100000000000000 : ℝ)*(base19) + (392342821/25000000000000 : ℝ)*(base23) + (57810789/50000000000000 : ℝ)*(base24) + (385689407/100000000000000 : ℝ)*(upper3) + (148024825573541/25000000000000 : ℝ)*(major0) + (148024825573541/25000000000000 : ℝ)*(major1) + (148024825573541/25000000000000 : ℝ)*(major2) + (394500443319379/50000000000000 : ℝ)*(sp0) + (197250711537403/25000000000000 : ℝ)*(sp1) + (197250711465881/25000000000000 : ℝ)*(sp2) + (790381628837/200000000000 : ℝ)*(sp3) + (743402009/20000000000000 : ℝ)*(sp4) + (369849851/12500000000000 : ℝ)*(sp7) + (197596923004863/50000000000000 : ℝ)*(f.failure) + (394502265428193/50000000000000 : ℝ)*(f.sum) + (38989257936369/25000000000000000000000000000 : ℝ)*base65 + (209063706661369/50000000000000000000000000000 : ℝ)*base67 + (38132639138631/50000000000000000000000000000 : ℝ)*base70 + (235194123511369/50000000000000000000000000000 : ℝ)*base71 + (8555005088631/25000000000000000000000000000 : ℝ)*base74 + (350067996711369/50000000000000000000000000000 : ℝ)*base75 + (131653380088631/50000000000000000000000000000 : ℝ)*base78 + (73715932888631/50000000000000000000000000000 : ℝ)*base80 + (121505743388631/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (12125753/5000000000000000000000 : ℝ)*base89 + (12125753/5000000000000000000000 : ℝ)*base91 + (12125753/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (360939038095422498517761/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49916521/100000000000000 : ℝ)*(base1) + (1755551/195312500000 : ℝ)*(base19) + (27957517/3125000000000 : ℝ)*(base23) + (18364319/20000000000000 : ℝ)*(upper3) + (109531069/100000000000000 : ℝ)*(upper5) + (624891361890657/100000000000000 : ℝ)*(major0) + (624891361890657/100000000000000 : ℝ)*(major1) + (624891361890657/100000000000000 : ℝ)*(major2) + (222564747/12500000000000 : ℝ)*(sp1) + (1780293291/100000000000000 : ℝ)*(sp2) + (52043869007099/6250000000000 : ℝ)*(sp4) + (52043698427311/6250000000000 : ℝ)*(sp5) + (208174794815807/25000000000000 : ℝ)*(sp6) + (52135087419339/12500000000000 : ℝ)*(sp7) + (417080749271233/100000000000000 : ℝ)*(f.failure) + (104087731774633/12500000000000 : ℝ)*(f.sum) + (38232310672587/100000000000000000000000000000 : ℝ)*base66 + (247600051727413/200000000000000000000000000000 : ℝ)*base67 + (58680837327413/200000000000000000000000000000 : ℝ)*base69 + (786952858672587/200000000000000000000000000000 : ℝ)*base72 + (272550898927413/100000000000000000000000000000 : ℝ)*base73 + (1737262901872587/200000000000000000000000000000 : ℝ)*base76 + (372160378672587/200000000000000000000000000000 : ℝ)*base78 + (307001020727413/200000000000000000000000000000 : ℝ)*base79 + (119581369727413/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (11633223/10000000000000000000000 : ℝ)*base89 + (11633223/10000000000000000000000 : ℝ)*base91 + (11633223/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1160_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13873/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1160_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1160_s1_0 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-83579661/400000000 : ℝ)*x 0 + (2848360823/5000000000 : ℝ)*x 1 + (1001202893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83579661/400000000 : ℝ)^8353 ≤ (12565365868299/100000000000000 : ℝ)^6305 := by
    have hnat : (83579661 : ℕ)^8353*100000000000000^6305 ≤ 12565365868299^6305*400000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83579661 400000000 12565365868299 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2848360823/5000000000 : ℝ)^8353 ≤ (23725574224389/50000000000000 : ℝ)^6305 := by
    have hnat : (2848360823 : ℕ)^8353*50000000000000^6305 ≤ 23725574224389^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848360823 5000000000 23725574224389 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001202893/2000000000 : ℝ)^8353 ≤ (799669713513/2000000000000 : ℝ)^6305 := by
    have hnat : (1001202893 : ℕ)^8353*2000000000000^6305 ≤ 799669713513^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001202893 2000000000 799669713513 2000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83579661/400000000 : ℝ), (2848360823/5000000000 : ℝ), (1001202893/2000000000 : ℝ)] ![(12565365868299/100000000000000 : ℝ), (23725574224389/50000000000000 : ℝ), (799669713513/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83579661/400000000 : ℝ)|^8353 ≤ (12565365868299/100000000000000 : ℝ)^6305
        have hw : |(-83579661/400000000 : ℝ)|=(83579661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2848360823/5000000000 : ℝ)|^8353 ≤ (23725574224389/50000000000000 : ℝ)^6305
        have hw : |(2848360823/5000000000 : ℝ)|=(2848360823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001202893/2000000000 : ℝ)|^8353 ≤ (799669713513/2000000000000 : ℝ)^6305
        have hw : |(1001202893/2000000000 : ℝ)|=(1001202893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s1_1 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5418133287/10000000000 : ℝ)*x 0 + (-1230947487/5000000000 : ℝ)*x 1 + (1251503381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5418133287/10000000000 : ℝ)^8353 ≤ (44401569440149/100000000000000 : ℝ)^6305 := by
    have hnat : (5418133287 : ℕ)^8353*100000000000000^6305 ≤ 44401569440149^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418133287 10000000000 44401569440149 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1230947487/5000000000 : ℝ)^8353 ≤ (7807477409073/50000000000000 : ℝ)^6305 := by
    have hnat : (1230947487 : ℕ)^8353*50000000000000^6305 ≤ 7807477409073^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230947487 5000000000 7807477409073 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251503381/2500000000 : ℝ)^8353 ≤ (4997934464811/12500000000000 : ℝ)^6305 := by
    have hnat : (1251503381 : ℕ)^8353*12500000000000^6305 ≤ 4997934464811^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251503381 2500000000 4997934464811 12500000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5418133287/10000000000 : ℝ), (-1230947487/5000000000 : ℝ), (1251503381/2500000000 : ℝ)] ![(44401569440149/100000000000000 : ℝ), (7807477409073/50000000000000 : ℝ), (4997934464811/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5418133287/10000000000 : ℝ)|^8353 ≤ (44401569440149/100000000000000 : ℝ)^6305
        have hw : |(5418133287/10000000000 : ℝ)|=(5418133287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1230947487/5000000000 : ℝ)|^8353 ≤ (7807477409073/50000000000000 : ℝ)^6305
        have hw : |(-1230947487/5000000000 : ℝ)|=(1230947487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1251503381/2500000000 : ℝ)|^8353 ≤ (4997934464811/12500000000000 : ℝ)^6305
        have hw : |(1251503381/2500000000 : ℝ)|=(1251503381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s1_2 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (169316731/312500000 : ℝ)*x 0 + (156437863/312500000 : ℝ)*x 1 + (-1230947329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169316731/312500000 : ℝ)^8353 ≤ (8880318458787/20000000000000 : ℝ)^6305 := by
    have hnat : (169316731 : ℕ)^8353*20000000000000^6305 ≤ 8880318458787^6305*312500000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169316731 312500000 8880318458787 20000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156437863/312500000 : ℝ)^8353 ≤ (39983455529049/100000000000000 : ℝ)^6305 := by
    have hnat : (156437863 : ℕ)^8353*100000000000000^6305 ≤ 39983455529049^6305*312500000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156437863 312500000 39983455529049 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1230947329/5000000000 : ℝ)^8353 ≤ (15614952162833/100000000000000 : ℝ)^6305 := by
    have hnat : (1230947329 : ℕ)^8353*100000000000000^6305 ≤ 15614952162833^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230947329 5000000000 15614952162833 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169316731/312500000 : ℝ), (156437863/312500000 : ℝ), (-1230947329/5000000000 : ℝ)] ![(8880318458787/20000000000000 : ℝ), (39983455529049/100000000000000 : ℝ), (15614952162833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169316731/312500000 : ℝ)|^8353 ≤ (8880318458787/20000000000000 : ℝ)^6305
        have hw : |(169316731/312500000 : ℝ)|=(169316731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156437863/312500000 : ℝ)|^8353 ≤ (39983455529049/100000000000000 : ℝ)^6305
        have hw : |(156437863/312500000 : ℝ)|=(156437863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1230947329/5000000000 : ℝ)|^8353 ≤ (15614952162833/100000000000000 : ℝ)^6305
        have hw : |(-1230947329/5000000000 : ℝ)|=(1230947329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s1_3 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1078977901/2500000000 : ℝ)*x 0 + (1840205901/5000000000 : ℝ)*x 1 + (252970241/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078977901/2500000000 : ℝ)^8353 ≤ (32850064827017/100000000000000 : ℝ)^6305 := by
    have hnat : (1078977901 : ℕ)^8353*100000000000000^6305 ≤ 32850064827017^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078977901 2500000000 32850064827017 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1840205901/5000000000 : ℝ)^8353 ≤ (13300262449041/50000000000000 : ℝ)^6305 := by
    have hnat : (1840205901 : ℕ)^8353*50000000000000^6305 ≤ 13300262449041^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840205901 5000000000 13300262449041 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252970241/500000000 : ℝ)^8353 ≤ (20274705135629/50000000000000 : ℝ)^6305 := by
    have hnat : (252970241 : ℕ)^8353*50000000000000^6305 ≤ 20274705135629^6305*500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252970241 500000000 20274705135629 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078977901/2500000000 : ℝ), (1840205901/5000000000 : ℝ), (252970241/500000000 : ℝ)] ![(32850064827017/100000000000000 : ℝ), (13300262449041/50000000000000 : ℝ), (20274705135629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078977901/2500000000 : ℝ)|^8353 ≤ (32850064827017/100000000000000 : ℝ)^6305
        have hw : |(1078977901/2500000000 : ℝ)|=(1078977901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1840205901/5000000000 : ℝ)|^8353 ≤ (13300262449041/50000000000000 : ℝ)^6305
        have hw : |(1840205901/5000000000 : ℝ)|=(1840205901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252970241/500000000 : ℝ)|^8353 ≤ (20274705135629/50000000000000 : ℝ)^6305
        have hw : |(252970241/500000000 : ℝ)|=(252970241/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s1_4 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045138653/5000000000 : ℝ)*x 0 + (626922603/1250000000 : ℝ)*x 1 + (5687167709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045138653/5000000000 : ℝ)^8353 ≤ (12571626526017/100000000000000 : ℝ)^6305 := by
    have hnat : (1045138653 : ℕ)^8353*100000000000000^6305 ≤ 12571626526017^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045138653 5000000000 12571626526017 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626922603/1250000000 : ℝ)^8353 ≤ (313145512597/781250000000 : ℝ)^6305 := by
    have hnat : (626922603 : ℕ)^8353*781250000000^6305 ≤ 313145512597^6305*1250000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626922603 1250000000 313145512597 781250000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5687167709/10000000000 : ℝ)^8353 ≤ (47345747835189/100000000000000 : ℝ)^6305 := by
    have hnat : (5687167709 : ℕ)^8353*100000000000000^6305 ≤ 47345747835189^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5687167709 10000000000 47345747835189 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045138653/5000000000 : ℝ), (626922603/1250000000 : ℝ), (5687167709/10000000000 : ℝ)] ![(12571626526017/100000000000000 : ℝ), (313145512597/781250000000 : ℝ), (47345747835189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045138653/5000000000 : ℝ)|^8353 ≤ (12571626526017/100000000000000 : ℝ)^6305
        have hw : |(-1045138653/5000000000 : ℝ)|=(1045138653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(626922603/1250000000 : ℝ)|^8353 ≤ (313145512597/781250000000 : ℝ)^6305
        have hw : |(626922603/1250000000 : ℝ)|=(626922603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5687167709/10000000000 : ℝ)|^8353 ≤ (47345747835189/100000000000000 : ℝ)^6305
        have hw : |(5687167709/10000000000 : ℝ)|=(5687167709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s1_5 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2620444759/5000000000 : ℝ)*x 0 + (-1780737119/10000000000 : ℝ)*x 1 + (56871711/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620444759/5000000000 : ℝ)^8353 ≤ (2124377543281/5000000000000 : ℝ)^6305 := by
    have hnat : (2620444759 : ℕ)^8353*5000000000000^6305 ≤ 2124377543281^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620444759 5000000000 2124377543281 5000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1780737119/10000000000 : ℝ)^8353 ≤ (5083331940637/50000000000000 : ℝ)^6305 := by
    have hnat : (1780737119 : ℕ)^8353*50000000000000^6305 ≤ 5083331940637^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780737119 10000000000 5083331940637 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56871711/100000000 : ℝ)^8353 ≤ (23672892617533/50000000000000 : ℝ)^6305 := by
    have hnat : (56871711 : ℕ)^8353*50000000000000^6305 ≤ 23672892617533^6305*100000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56871711 100000000 23672892617533 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620444759/5000000000 : ℝ), (-1780737119/10000000000 : ℝ), (56871711/100000000 : ℝ)] ![(2124377543281/5000000000000 : ℝ), (5083331940637/50000000000000 : ℝ), (23672892617533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620444759/5000000000 : ℝ)|^8353 ≤ (2124377543281/5000000000000 : ℝ)^6305
        have hw : |(2620444759/5000000000 : ℝ)|=(2620444759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1780737119/10000000000 : ℝ)|^8353 ≤ (5083331940637/50000000000000 : ℝ)^6305
        have hw : |(-1780737119/10000000000 : ℝ)|=(1780737119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56871711/100000000 : ℝ)|^8353 ≤ (23672892617533/50000000000000 : ℝ)^6305
        have hw : |(56871711/100000000 : ℝ)|=(56871711/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s1_6 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5240888511/10000000000 : ℝ)*x 0 + (5687172613/10000000000 : ℝ)*x 1 + (-890368171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5240888511/10000000000 : ℝ)^8353 ≤ (42487540050197/100000000000000 : ℝ)^6305 := by
    have hnat : (5240888511 : ℕ)^8353*100000000000000^6305 ≤ 42487540050197^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240888511 10000000000 42487540050197 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5687172613/10000000000 : ℝ)^8353 ≤ (9469160384437/20000000000000 : ℝ)^6305 := by
    have hnat : (5687172613 : ℕ)^8353*20000000000000^6305 ≤ 9469160384437^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5687172613 10000000000 9469160384437 20000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890368171/5000000000 : ℝ)^8353 ≤ (317708062633/3125000000000 : ℝ)^6305 := by
    have hnat : (890368171 : ℕ)^8353*3125000000000^6305 ≤ 317708062633^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890368171 5000000000 317708062633 3125000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5240888511/10000000000 : ℝ), (5687172613/10000000000 : ℝ), (-890368171/5000000000 : ℝ)] ![(42487540050197/100000000000000 : ℝ), (9469160384437/20000000000000 : ℝ), (317708062633/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5240888511/10000000000 : ℝ)|^8353 ≤ (42487540050197/100000000000000 : ℝ)^6305
        have hw : |(5240888511/10000000000 : ℝ)|=(5240888511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5687172613/10000000000 : ℝ)|^8353 ≤ (9469160384437/20000000000000 : ℝ)^6305
        have hw : |(5687172613/10000000000 : ℝ)|=(5687172613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-890368171/5000000000 : ℝ)|^8353 ≤ (317708062633/3125000000000 : ℝ)^6305
        have hw : |(-890368171/5000000000 : ℝ)|=(890368171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s1_7 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (269841797/625000000 : ℝ)*x 0 + (5040706819/10000000000 : ℝ)*x 1 + (924869389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269841797/625000000 : ℝ)^8353 ≤ (32865767602381/100000000000000 : ℝ)^6305 := by
    have hnat : (269841797 : ℕ)^8353*100000000000000^6305 ≤ 32865767602381^6305*625000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269841797 625000000 32865767602381 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5040706819/10000000000 : ℝ)^8353 ≤ (5043874282569/12500000000000 : ℝ)^6305 := by
    have hnat : (5040706819 : ℕ)^8353*12500000000000^6305 ≤ 5043874282569^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5040706819 10000000000 5043874282569 12500000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924869389/2500000000 : ℝ)^8353 ≤ (26783238121369/100000000000000 : ℝ)^6305 := by
    have hnat : (924869389 : ℕ)^8353*100000000000000^6305 ≤ 26783238121369^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924869389 2500000000 26783238121369 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269841797/625000000 : ℝ), (5040706819/10000000000 : ℝ), (924869389/2500000000 : ℝ)] ![(32865767602381/100000000000000 : ℝ), (5043874282569/12500000000000 : ℝ), (26783238121369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269841797/625000000 : ℝ)|^8353 ≤ (32865767602381/100000000000000 : ℝ)^6305
        have hw : |(269841797/625000000 : ℝ)|=(269841797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5040706819/10000000000 : ℝ)|^8353 ≤ (5043874282569/12500000000000 : ℝ)^6305
        have hw : |(5040706819/10000000000 : ℝ)|=(5040706819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(924869389/2500000000 : ℝ)|^8353 ≤ (26783238121369/100000000000000 : ℝ)^6305
        have hw : |(924869389/2500000000 : ℝ)|=(924869389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1160_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13873/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (23/400 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5089/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13873/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13873/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13873/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13873/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13873/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13873/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (487/100000 : ℝ) ^ (261/64 : ℝ) ≤ (18553423133/50000000000000000000 : ℝ) := by
    have hpowers : (487/100000 : ℝ)^261 ≤ (18553423133/50000000000000000000 : ℝ)^64 := by
      have hnat : (487 : ℕ)^261*50000000000000000000^64 ≤ 18553423133^64*100000^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        487 100000 18553423133 50000000000000000000 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (487/100000 : ℝ)) (X := (18553423133/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hpowhi : (13873/50000 : ℝ) ^ (261/64 : ℝ) ≤ (536168823563762321/100000000000000000000 : ℝ) := by
    have hpowers : (13873/50000 : ℝ)^261 ≤ (536168823563762321/100000000000000000000 : ℝ)^64 := by
      have hnat : (13873 : ℕ)^261*100000000000000000000^64 ≤ 536168823563762321^64*50000^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13873 50000 536168823563762321 100000000000000000000 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13873/50000 : ℝ)) (X := (536168823563762321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000018553423133/25000000000000000000 : ℝ) ≤ (50000000009099/50000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (25000000018553423133/25000000000000000000 : ℝ)^64 ≤ (50000000009099/50000000000000 : ℝ)^261 := by
      have hnat : (25000000018553423133 : ℕ)^64*50000000000000^261 ≤ 50000000009099^261*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000018553423133 25000000000000000000 50000000009099 50000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50000000009099/50000000000000 : ℝ)) (X := (25000000018553423133/25000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100536168860670608587/100000000000000000000 : ℝ) ≤ (5006560457658221/5000000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (100536168860670608587/100000000000000000000 : ℝ)^64 ≤ (5006560457658221/5000000000000000 : ℝ)^261 := by
      have hnat : (100536168860670608587 : ℕ)^64*5000000000000000^261 ≤ 5006560457658221^261*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100536168860670608587 100000000000000000000 5006560457658221 5000000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006560457658221/5000000000000000 : ℝ)) (X := (100536168860670608587/100000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50536168823563762321/50000000000000000000 : ℝ) ≤ (2506560457203271/2500000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (50536168823563762321/50000000000000000000 : ℝ)^64 ≤ (2506560457203271/2500000000000000 : ℝ)^261 := by
      have hnat : (50536168823563762321 : ℕ)^64*2500000000000000^261 ≤ 2506560457203271^261*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50536168823563762321 50000000000000000000 2506560457203271 2500000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506560457203271/2500000000000000 : ℝ)) (X := (50536168823563762321/50000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(18553423133/50000000000000000000 : ℝ) ≤ ((68144305069965049723/68147500000000000000 : ℝ)+2*(6560456748321/1362950000000000 : ℝ)*(487/100000 : ℝ))^(261/64 : ℝ) := by
    rw [show (68144305069965049723/68147500000000000000 : ℝ)+2*(6560456748321/1362950000000000 : ℝ)*(487/100000 : ℝ)=(50000000009099/50000000000000 : ℝ) by norm_num, show 1+2*(18553423133/50000000000000000000 : ℝ)=(25000000018553423133/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(536168823563762321/100000000000000000000 : ℝ)+(18553423133/50000000000000000000 : ℝ) ≤ ((68144305069965049723/68147500000000000000 : ℝ)+(6560456748321/1362950000000000 : ℝ)*((13873/50000 : ℝ)+(487/100000 : ℝ)))^(261/64 : ℝ) := by
    rw [show (68144305069965049723/68147500000000000000 : ℝ)+(6560456748321/1362950000000000 : ℝ)*((13873/50000 : ℝ)+(487/100000 : ℝ))=(5006560457658221/5000000000000000 : ℝ) by norm_num, show 1+(536168823563762321/100000000000000000000 : ℝ)+(18553423133/50000000000000000000 : ℝ)=(100536168860670608587/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(536168823563762321/100000000000000000000 : ℝ) ≤ ((68144305069965049723/68147500000000000000 : ℝ)+2*(6560456748321/1362950000000000 : ℝ)*(13873/50000 : ℝ))^(261/64 : ℝ) := by
    rw [show (68144305069965049723/68147500000000000000 : ℝ)+2*(6560456748321/1362950000000000 : ℝ)*(13873/50000 : ℝ)=(2506560457203271/2500000000000000 : ℝ) by norm_num, show 1+2*(536168823563762321/100000000000000000000 : ℝ)=(50536168823563762321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68144305069965049723/68147500000000000000 : ℝ)*(X 1 0+X 2 0)+(6560456748321/1362950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (487/100000 : ℝ)) (hi := (13873/50000 : ℝ)) (c := (68144305069965049723/68147500000000000000 : ℝ)) (alpha := (6560456748321/1362950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68144305069965049723/68147500000000000000 : ℝ)*(X 0 1+X 2 1)+(6560456748321/1362950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (487/100000 : ℝ)) (hi := (13873/50000 : ℝ)) (c := (68144305069965049723/68147500000000000000 : ℝ)) (alpha := (6560456748321/1362950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68144305069965049723/68147500000000000000 : ℝ)*(X 0 2+X 1 2)+(6560456748321/1362950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (487/100000 : ℝ)) (hi := (13873/50000 : ℝ)) (c := (68144305069965049723/68147500000000000000 : ℝ)) (alpha := (6560456748321/1362950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-83579661/400000000 : ℝ)*X 0 0+(2848360823/5000000000 : ℝ)*X 0 1+(1001202893/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5418133287/10000000000 : ℝ)*X 1 0+(-1230947487/5000000000 : ℝ)*X 1 1+(1251503381/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((169316731/312500000 : ℝ)*X 2 0+(156437863/312500000 : ℝ)*X 2 1+(-1230947329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1078977901/2500000000 : ℝ)*X 0 0+(1840205901/5000000000 : ℝ)*X 0 1+(252970241/500000000 : ℝ)*X 0 2+(1078977901/2500000000 : ℝ)*X 1 0+(1840205901/5000000000 : ℝ)*X 1 1+(252970241/500000000 : ℝ)*X 1 2+(1078977901/2500000000 : ℝ)*X 2 0+(1840205901/5000000000 : ℝ)*X 2 1+(252970241/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1045138653/5000000000 : ℝ)*X 0 0+(626922603/1250000000 : ℝ)*X 0 1+(5687167709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2620444759/5000000000 : ℝ)*X 1 0+(-1780737119/10000000000 : ℝ)*X 1 1+(56871711/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5240888511/10000000000 : ℝ)*X 2 0+(5687172613/10000000000 : ℝ)*X 2 1+(-890368171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((269841797/625000000 : ℝ)*X 0 0+(5040706819/10000000000 : ℝ)*X 0 1+(924869389/2500000000 : ℝ)*X 0 2+(269841797/625000000 : ℝ)*X 1 0+(5040706819/10000000000 : ℝ)*X 1 1+(924869389/2500000000 : ℝ)*X 1 2+(269841797/625000000 : ℝ)*X 2 0+(5040706819/10000000000 : ℝ)*X 2 1+(924869389/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (911612021233720003964453559/425921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52403529/25000000000000 : ℝ)*(base1) + (725997007/100000000000000 : ℝ)*(base19) + (363108813/50000000000000 : ℝ)*(base23) + (25191751/20000000000000 : ℝ)*(base37) + (274848089/100000000000000 : ℝ)*(lower2) + (271619706360811/25000000000000 : ℝ)*(major0) + (271619706360811/25000000000000 : ℝ)*(major1) + (271619706360811/25000000000000 : ℝ)*(major2) + (361947728493197/25000000000000 : ℝ)*(sp0) + (1447791760508661/100000000000000 : ℝ)*(sp1) + (1447790079438003/100000000000000 : ℝ)*(sp2) + (145032951492743/20000000000000 : ℝ)*(sp3) + (1782146997/100000000000000 : ℝ)*(sp4) + (42021251/2500000000000 : ℝ)*(sp6) + (362582546518293/50000000000000 : ℝ)*(f.failure) + (361948121626417/25000000000000 : ℝ)*(f.sum) + (205836849120319/68147500000000000000000000000 : ℝ)*base65 + (10067301319374469647/1703687500000000000000000000000000 : ℝ)*base68 + (3687989289126532147/1703687500000000000000000000000000 : ℝ)*base70 + (2620020809643157147/1703687500000000000000000000000000 : ℝ)*base72 + (19313485225067/8518437500000000000000000000 : ℝ)*base74 + (5322757555724155353/1703687500000000000000000000000000 : ℝ)*base75 + (3741207176232594647/1703687500000000000000000000000000 : ℝ)*base78 + (10510673711069969647/1703687500000000000000000000000000 : ℝ)*base80 + (277229017330039/68147500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (9207917/5000000000000000000000 : ℝ)*base90 + (9207917/5000000000000000000000 : ℝ)*base92 + (9207917/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (247283739440900986805163039/851843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1847813639/100000000000000 : ℝ)*(base19) + (2550536179/100000000000000 : ℝ)*(base23) + (406301831/100000000000000 : ℝ)*(upper2) + (561307649/100000000000000 : ℝ)*(upper3) + (34945421/12500000000000 : ℝ)*(upper5) + (558536761170231/50000000000000 : ℝ)*(major0) + (558536761170231/50000000000000 : ℝ)*(major1) + (558536761170231/50000000000000 : ℝ)*(major2) + (10869643703/100000000000000 : ℝ)*(sp1) + (34363691/200000000000 : ℝ)*(sp2) + (372140414481313/25000000000000 : ℝ)*(sp4) + (1488548940467909/100000000000000 : ℝ)*(sp5) + (1488541925543573/100000000000000 : ℝ)*(sp6) + (93198172134907/12500000000000 : ℝ)*(sp7) + (93198172134907/12500000000000 : ℝ)*(f.failure) + (372140414481313/25000000000000 : ℝ)*(f.sum) + (39969403626099/34073750000000000000000000000 : ℝ)*base66 + (5988605857161053987/3407375000000000000000000000000000 : ℝ)*base68 + (24189616291189553987/3407375000000000000000000000000000 : ℝ)*base70 + (11612824080194321013/3407375000000000000000000000000000 : ℝ)*base71 + (93071407660159/136295000000000000000000000000 : ℝ)*base73 + (2762616659119053987/3407375000000000000000000000000000 : ℝ)*base76 + (13069540002383178987/3407375000000000000000000000000000 : ℝ)*base78 + (20691178884243428987/3407375000000000000000000000000000 : ℝ)*base80 + (33648389177773/68147500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2457117/1250000000000000000000 : ℝ)*base89 + (2457117/1250000000000000000000 : ℝ)*base91 + (2457117/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1160_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13873/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (23/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5089/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1160_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1160_s2_0 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-428352111/2000000000 : ℝ)*x 0 + (1376853383/2500000000 : ℝ)*x 1 + (2581034119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428352111/2000000000 : ℝ)^8353 ≤ (6491736422379/50000000000000 : ℝ)^6305 := by
    have hnat : (428352111 : ℕ)^8353*50000000000000^6305 ≤ 6491736422379^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428352111 2000000000 6491736422379 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376853383/2500000000 : ℝ)^8353 ≤ (45373461072093/100000000000000 : ℝ)^6305 := by
    have hnat : (1376853383 : ℕ)^8353*100000000000000^6305 ≤ 45373461072093^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376853383 2500000000 45373461072093 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2581034119/5000000000 : ℝ)^8353 ≤ (41643066066547/100000000000000 : ℝ)^6305 := by
    have hnat : (2581034119 : ℕ)^8353*100000000000000^6305 ≤ 41643066066547^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581034119 5000000000 41643066066547 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428352111/2000000000 : ℝ), (1376853383/2500000000 : ℝ), (2581034119/5000000000 : ℝ)] ![(6491736422379/50000000000000 : ℝ), (45373461072093/100000000000000 : ℝ), (41643066066547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428352111/2000000000 : ℝ)|^8353 ≤ (6491736422379/50000000000000 : ℝ)^6305
        have hw : |(-428352111/2000000000 : ℝ)|=(428352111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376853383/2500000000 : ℝ)|^8353 ≤ (45373461072093/100000000000000 : ℝ)^6305
        have hw : |(1376853383/2500000000 : ℝ)|=(1376853383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2581034119/5000000000 : ℝ)|^8353 ≤ (41643066066547/100000000000000 : ℝ)^6305
        have hw : |(2581034119/5000000000 : ℝ)|=(2581034119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s2_1 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5373093607/10000000000 : ℝ)*x 0 + (-580295123/2500000000 : ℝ)*x 1 + (5162070763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373093607/10000000000 : ℝ)^8353 ≤ (43913239343617/100000000000000 : ℝ)^6305 := by
    have hnat : (5373093607 : ℕ)^8353*100000000000000^6305 ≤ 43913239343617^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373093607 10000000000 43913239343617 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (580295123/2500000000 : ℝ)^8353 ≤ (1805458448169/12500000000000 : ℝ)^6305 := by
    have hnat : (580295123 : ℕ)^8353*12500000000000^6305 ≤ 1805458448169^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580295123 2500000000 1805458448169 12500000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5162070763/10000000000 : ℝ)^8353 ≤ (41643093052501/100000000000000 : ℝ)^6305 := by
    have hnat : (5162070763 : ℕ)^8353*100000000000000^6305 ≤ 41643093052501^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162070763 10000000000 41643093052501 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373093607/10000000000 : ℝ), (-580295123/2500000000 : ℝ), (5162070763/10000000000 : ℝ)] ![(43913239343617/100000000000000 : ℝ), (1805458448169/12500000000000 : ℝ), (41643093052501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373093607/10000000000 : ℝ)|^8353 ≤ (43913239343617/100000000000000 : ℝ)^6305
        have hw : |(5373093607/10000000000 : ℝ)|=(5373093607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-580295123/2500000000 : ℝ)|^8353 ≤ (1805458448169/12500000000000 : ℝ)^6305
        have hw : |(-580295123/2500000000 : ℝ)|=(580295123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5162070763/10000000000 : ℝ)|^8353 ≤ (41643093052501/100000000000000 : ℝ)^6305
        have hw : |(5162070763/10000000000 : ℝ)|=(5162070763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s2_2 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1074618781/2000000000 : ℝ)*x 0 + (5162070171/10000000000 : ℝ)*x 1 + (-580295217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074618781/2000000000 : ℝ)^8353 ≤ (21956621285107/50000000000000 : ℝ)^6305 := by
    have hnat : (1074618781 : ℕ)^8353*50000000000000^6305 ≤ 21956621285107^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074618781 2000000000 21956621285107 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5162070171/10000000000 : ℝ)^8353 ≤ (41643086725497/100000000000000 : ℝ)^6305 := by
    have hnat : (5162070171 : ℕ)^8353*100000000000000^6305 ≤ 41643086725497^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162070171 10000000000 41643086725497 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (580295217/2500000000 : ℝ)^8353 ≤ (1444367068501/10000000000000 : ℝ)^6305 := by
    have hnat : (580295217 : ℕ)^8353*10000000000000^6305 ≤ 1444367068501^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580295217 2500000000 1444367068501 10000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074618781/2000000000 : ℝ), (5162070171/10000000000 : ℝ), (-580295217/2500000000 : ℝ)] ![(21956621285107/50000000000000 : ℝ), (41643086725497/100000000000000 : ℝ), (1444367068501/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074618781/2000000000 : ℝ)|^8353 ≤ (21956621285107/50000000000000 : ℝ)^6305
        have hw : |(1074618781/2000000000 : ℝ)|=(1074618781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5162070171/10000000000 : ℝ)|^8353 ≤ (41643086725497/100000000000000 : ℝ)^6305
        have hw : |(5162070171/10000000000 : ℝ)|=(5162070171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-580295217/2500000000 : ℝ)|^8353 ≤ (1444367068501/10000000000000 : ℝ)^6305
        have hw : |(-580295217/2500000000 : ℝ)|=(580295217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s2_3 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271988479/625000000 : ℝ)*x 0 + (2010276499/5000000000 : ℝ)*x 1 + (4710030227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271988479/625000000 : ℝ)^8353 ≤ (16606299906953/50000000000000 : ℝ)^6305 := by
    have hnat : (271988479 : ℕ)^8353*50000000000000^6305 ≤ 16606299906953^6305*625000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271988479 625000000 16606299906953 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010276499/5000000000 : ℝ)^8353 ≤ (14952688463767/50000000000000 : ℝ)^6305 := by
    have hnat : (2010276499 : ℕ)^8353*50000000000000^6305 ≤ 14952688463767^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010276499 5000000000 14952688463767 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4710030227/10000000000 : ℝ)^8353 ≤ (18441011622257/50000000000000 : ℝ)^6305 := by
    have hnat : (4710030227 : ℕ)^8353*50000000000000^6305 ≤ 18441011622257^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4710030227 10000000000 18441011622257 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271988479/625000000 : ℝ), (2010276499/5000000000 : ℝ), (4710030227/10000000000 : ℝ)] ![(16606299906953/50000000000000 : ℝ), (14952688463767/50000000000000 : ℝ), (18441011622257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271988479/625000000 : ℝ)|^8353 ≤ (16606299906953/50000000000000 : ℝ)^6305
        have hw : |(271988479/625000000 : ℝ)|=(271988479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010276499/5000000000 : ℝ)|^8353 ≤ (14952688463767/50000000000000 : ℝ)^6305
        have hw : |(2010276499/5000000000 : ℝ)|=(2010276499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4710030227/10000000000 : ℝ)|^8353 ≤ (18441011622257/50000000000000 : ℝ)^6305
        have hw : |(4710030227/10000000000 : ℝ)|=(4710030227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s2_4 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070928853/5000000000 : ℝ)*x 0 + (2582210161/5000000000 : ℝ)*x 1 + (1101007717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070928853/5000000000 : ℝ)^8353 ≤ (12984253084061/100000000000000 : ℝ)^6305 := by
    have hnat : (1070928853 : ℕ)^8353*100000000000000^6305 ≤ 12984253084061^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070928853 5000000000 12984253084061 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2582210161/5000000000 : ℝ)^8353 ≤ (10417051459267/25000000000000 : ℝ)^6305 := by
    have hnat : (2582210161 : ℕ)^8353*25000000000000^6305 ≤ 10417051459267^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582210161 5000000000 10417051459267 25000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101007717/2000000000 : ℝ)^8353 ≤ (45347541065151/100000000000000 : ℝ)^6305 := by
    have hnat : (1101007717 : ℕ)^8353*100000000000000^6305 ≤ 45347541065151^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101007717 2000000000 45347541065151 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070928853/5000000000 : ℝ), (2582210161/5000000000 : ℝ), (1101007717/2000000000 : ℝ)] ![(12984253084061/100000000000000 : ℝ), (10417051459267/25000000000000 : ℝ), (45347541065151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070928853/5000000000 : ℝ)|^8353 ≤ (12984253084061/100000000000000 : ℝ)^6305
        have hw : |(-1070928853/5000000000 : ℝ)|=(1070928853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2582210161/5000000000 : ℝ)|^8353 ≤ (10417051459267/25000000000000 : ℝ)^6305
        have hw : |(2582210161/5000000000 : ℝ)|=(2582210161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101007717/2000000000 : ℝ)|^8353 ≤ (45347541065151/100000000000000 : ℝ)^6305
        have hw : |(1101007717/2000000000 : ℝ)|=(1101007717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s2_5 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528536561/1000000000 : ℝ)*x 0 + (-395642321/2000000000 : ℝ)*x 1 + (5505038577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528536561/1000000000 : ℝ)^8353 ≤ (10741473000709/25000000000000 : ℝ)^6305 := by
    have hnat : (528536561 : ℕ)^8353*25000000000000^6305 ≤ 10741473000709^6305*1000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528536561 1000000000 10741473000709 25000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395642321/2000000000 : ℝ)^8353 ≤ (11686567004593/100000000000000 : ℝ)^6305 := by
    have hnat : (395642321 : ℕ)^8353*100000000000000^6305 ≤ 11686567004593^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395642321 2000000000 11686567004593 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505038577/10000000000 : ℝ)^8353 ≤ (9069508195569/20000000000000 : ℝ)^6305 := by
    have hnat : (5505038577 : ℕ)^8353*20000000000000^6305 ≤ 9069508195569^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505038577 10000000000 9069508195569 20000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528536561/1000000000 : ℝ), (-395642321/2000000000 : ℝ), (5505038577/10000000000 : ℝ)] ![(10741473000709/25000000000000 : ℝ), (11686567004593/100000000000000 : ℝ), (9069508195569/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528536561/1000000000 : ℝ)|^8353 ≤ (10741473000709/25000000000000 : ℝ)^6305
        have hw : |(528536561/1000000000 : ℝ)|=(528536561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395642321/2000000000 : ℝ)|^8353 ≤ (11686567004593/100000000000000 : ℝ)^6305
        have hw : |(-395642321/2000000000 : ℝ)|=(395642321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505038577/10000000000 : ℝ)|^8353 ≤ (9069508195569/20000000000000 : ℝ)^6305
        have hw : |(5505038577/10000000000 : ℝ)|=(5505038577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s2_6 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (211414629/400000000 : ℝ)*x 0 + (5505038571/10000000000 : ℝ)*x 1 + (-395642291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211414629/400000000 : ℝ)^8353 ≤ (42965893241359/100000000000000 : ℝ)^6305 := by
    have hnat : (211414629 : ℕ)^8353*100000000000000^6305 ≤ 42965893241359^6305*400000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211414629 400000000 42965893241359 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5505038571/10000000000 : ℝ)^8353 ≤ (22673770456183/50000000000000 : ℝ)^6305 := by
    have hnat : (5505038571 : ℕ)^8353*50000000000000^6305 ≤ 22673770456183^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505038571 10000000000 22673770456183 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (395642291/2000000000 : ℝ)^8353 ≤ (11686565830607/100000000000000 : ℝ)^6305 := by
    have hnat : (395642291 : ℕ)^8353*100000000000000^6305 ≤ 11686565830607^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395642291 2000000000 11686565830607 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211414629/400000000 : ℝ), (5505038571/10000000000 : ℝ), (-395642291/2000000000 : ℝ)] ![(42965893241359/100000000000000 : ℝ), (22673770456183/50000000000000 : ℝ), (11686565830607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211414629/400000000 : ℝ)|^8353 ≤ (42965893241359/100000000000000 : ℝ)^6305
        have hw : |(211414629/400000000 : ℝ)|=(211414629/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5505038571/10000000000 : ℝ)|^8353 ≤ (22673770456183/50000000000000 : ℝ)^6305
        have hw : |(5505038571/10000000000 : ℝ)|=(5505038571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-395642291/2000000000 : ℝ)|^8353 ≤ (11686565830607/100000000000000 : ℝ)^6305
        have hw : |(-395642291/2000000000 : ℝ)|=(395642291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s2_7 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352011209/10000000000 : ℝ)*x 0 + (2352668329/5000000000 : ℝ)*x 1 + (503161479/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352011209/10000000000 : ℝ)^8353 ≤ (33214576964079/100000000000000 : ℝ)^6305 := by
    have hnat : (4352011209 : ℕ)^8353*100000000000000^6305 ≤ 33214576964079^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352011209 10000000000 33214576964079 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2352668329/5000000000 : ℝ)^8353 ≤ (1473333591853/4000000000000 : ℝ)^6305 := by
    have hnat : (2352668329 : ℕ)^8353*4000000000000^6305 ≤ 1473333591853^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2352668329 5000000000 1473333591853 4000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503161479/1250000000 : ℝ)^8353 ≤ (29952083229287/100000000000000 : ℝ)^6305 := by
    have hnat : (503161479 : ℕ)^8353*100000000000000^6305 ≤ 29952083229287^6305*1250000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503161479 1250000000 29952083229287 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352011209/10000000000 : ℝ), (2352668329/5000000000 : ℝ), (503161479/1250000000 : ℝ)] ![(33214576964079/100000000000000 : ℝ), (1473333591853/4000000000000 : ℝ), (29952083229287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352011209/10000000000 : ℝ)|^8353 ≤ (33214576964079/100000000000000 : ℝ)^6305
        have hw : |(4352011209/10000000000 : ℝ)|=(4352011209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2352668329/5000000000 : ℝ)|^8353 ≤ (1473333591853/4000000000000 : ℝ)^6305
        have hw : |(2352668329/5000000000 : ℝ)|=(2352668329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503161479/1250000000 : ℝ)|^8353 ≤ (29952083229287/100000000000000 : ℝ)^6305
        have hw : |(503161479/1250000000 : ℝ)|=(503161479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1160_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5089/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/400 : ℝ)*pair X i i ≤ pair X i h) :
    (9151/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16449/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5089/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (23/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5089/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (23/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5089/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (23/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5089/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (23/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5089/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (23/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5089/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (23/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (23/400 : ℝ) ^ (261/64 : ℝ) ≤ (874521375363061/100000000000000000000 : ℝ) := by
    have hpowers : (23/400 : ℝ)^261 ≤ (874521375363061/100000000000000000000 : ℝ)^64 := by
      have hnat : (23 : ℕ)^261*100000000000000000000^64 ≤ 874521375363061^64*400^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23 400 874521375363061 100000000000000000000 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23/400 : ℝ)) (X := (874521375363061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hpowhi : (5089/25000 : ℝ) ^ (261/64 : ℝ) ≤ (30324340290559413/20000000000000000000 : ℝ) := by
    have hpowers : (5089/25000 : ℝ)^261 ≤ (30324340290559413/20000000000000000000 : ℝ)^64 := by
      have hnat : (5089 : ℕ)^261*20000000000000000000^64 ≤ 30324340290559413^64*25000^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5089 25000 30324340290559413 20000000000000000000 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5089/25000 : ℝ)) (X := (30324340290559413/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000874521375363061/50000000000000000000 : ℝ) ≤ (10000042888121521/10000000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (50000874521375363061/50000000000000000000 : ℝ)^64 ≤ (10000042888121521/10000000000000000 : ℝ)^261 := by
      have hnat : (50000874521375363061 : ℕ)^64*10000000000000000^261 ≤ 10000042888121521^261*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000874521375363061 50000000000000000000 10000042888121521 10000000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000042888121521/10000000000000000 : ℝ)) (X := (50000874521375363061/50000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50076248111414080063/50000000000000000000 : ℝ) ≤ (2500934305210963/2500000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (50076248111414080063/50000000000000000000 : ℝ)^64 ≤ (2500934305210963/2500000000000000 : ℝ)^261 := by
      have hnat : (50076248111414080063 : ℕ)^64*2500000000000000^261 ≤ 2500934305210963^261*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50076248111414080063 50000000000000000000 2500934305210963 2500000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500934305210963/2500000000000000 : ℝ)) (X := (50076248111414080063/50000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (10030324340290559413/10000000000000000000 : ℝ) ≤ (10007431553566183/10000000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (10030324340290559413/10000000000000000000 : ℝ)^64 ≤ (10007431553566183/10000000000000000 : ℝ)^261 := by
      have hnat : (10030324340290559413 : ℕ)^64*10000000000000000^261 ≤ 10007431553566183^261*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10030324340290559413 10000000000000000000 10007431553566183 10000000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007431553566183/10000000000000000 : ℝ)) (X := (10030324340290559413/10000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(874521375363061/100000000000000000000 : ℝ) ≤ ((73009070798798064613/73030000000000000000 : ℝ)+2*(3694332722331/1460600000000000 : ℝ)*(23/400 : ℝ))^(261/64 : ℝ) := by
    rw [show (73009070798798064613/73030000000000000000 : ℝ)+2*(3694332722331/1460600000000000 : ℝ)*(23/400 : ℝ)=(10000042888121521/10000000000000000 : ℝ) by norm_num, show 1+2*(874521375363061/100000000000000000000 : ℝ)=(50000874521375363061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30324340290559413/20000000000000000000 : ℝ)+(874521375363061/100000000000000000000 : ℝ) ≤ ((73009070798798064613/73030000000000000000 : ℝ)+(3694332722331/1460600000000000 : ℝ)*((5089/25000 : ℝ)+(23/400 : ℝ)))^(261/64 : ℝ) := by
    rw [show (73009070798798064613/73030000000000000000 : ℝ)+(3694332722331/1460600000000000 : ℝ)*((5089/25000 : ℝ)+(23/400 : ℝ))=(2500934305210963/2500000000000000 : ℝ) by norm_num, show 1+(30324340290559413/20000000000000000000 : ℝ)+(874521375363061/100000000000000000000 : ℝ)=(50076248111414080063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30324340290559413/20000000000000000000 : ℝ) ≤ ((73009070798798064613/73030000000000000000 : ℝ)+2*(3694332722331/1460600000000000 : ℝ)*(5089/25000 : ℝ))^(261/64 : ℝ) := by
    rw [show (73009070798798064613/73030000000000000000 : ℝ)+2*(3694332722331/1460600000000000 : ℝ)*(5089/25000 : ℝ)=(10007431553566183/10000000000000000 : ℝ) by norm_num, show 1+2*(30324340290559413/20000000000000000000 : ℝ)=(10030324340290559413/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (73009070798798064613/73030000000000000000 : ℝ)*(X 1 0+X 2 0)+(3694332722331/1460600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (23/400 : ℝ)) (hi := (5089/25000 : ℝ)) (c := (73009070798798064613/73030000000000000000 : ℝ)) (alpha := (3694332722331/1460600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (73009070798798064613/73030000000000000000 : ℝ)*(X 0 1+X 2 1)+(3694332722331/1460600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (23/400 : ℝ)) (hi := (5089/25000 : ℝ)) (c := (73009070798798064613/73030000000000000000 : ℝ)) (alpha := (3694332722331/1460600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (73009070798798064613/73030000000000000000 : ℝ)*(X 0 2+X 1 2)+(3694332722331/1460600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (23/400 : ℝ)) (hi := (5089/25000 : ℝ)) (c := (73009070798798064613/73030000000000000000 : ℝ)) (alpha := (3694332722331/1460600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-428352111/2000000000 : ℝ)*X 0 0+(1376853383/2500000000 : ℝ)*X 0 1+(2581034119/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5373093607/10000000000 : ℝ)*X 1 0+(-580295123/2500000000 : ℝ)*X 1 1+(5162070763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074618781/2000000000 : ℝ)*X 2 0+(5162070171/10000000000 : ℝ)*X 2 1+(-580295217/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271988479/625000000 : ℝ)*X 0 0+(2010276499/5000000000 : ℝ)*X 0 1+(4710030227/10000000000 : ℝ)*X 0 2+(271988479/625000000 : ℝ)*X 1 0+(2010276499/5000000000 : ℝ)*X 1 1+(4710030227/10000000000 : ℝ)*X 1 2+(271988479/625000000 : ℝ)*X 2 0+(2010276499/5000000000 : ℝ)*X 2 1+(4710030227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1070928853/5000000000 : ℝ)*X 0 0+(2582210161/5000000000 : ℝ)*X 0 1+(1101007717/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528536561/1000000000 : ℝ)*X 1 0+(-395642321/2000000000 : ℝ)*X 1 1+(5505038577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211414629/400000000 : ℝ)*X 2 0+(5505038571/10000000000 : ℝ)*X 2 1+(-395642291/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352011209/10000000000 : ℝ)*X 0 0+(2352668329/5000000000 : ℝ)*X 0 1+(503161479/1250000000 : ℝ)*X 0 2+(4352011209/10000000000 : ℝ)*X 1 0+(2352668329/5000000000 : ℝ)*X 1 1+(503161479/1250000000 : ℝ)*X 1 2+(4352011209/10000000000 : ℝ)*X 2 0+(2352668329/5000000000 : ℝ)*X 2 1+(503161479/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (259671861121736524089369/36515000000000000000000000000 : ℝ) := by norm_num
    linear_combination (543938781/100000000000000 : ℝ)*(base19) + (539348309/100000000000000 : ℝ)*(base23) + (13088571/20000000000000 : ℝ)*(upper2) + (83346523/25000000000000 : ℝ)*(upper3) + (38550267/25000000000000 : ℝ)*(upper4) + (1086520335590811/50000000000000 : ℝ)*(major0) + (1086520335590811/50000000000000 : ℝ)*(major1) + (1086520335590811/50000000000000 : ℝ)*(major2) + (1447838118480621/50000000000000 : ℝ)*(sp0) + (115827798552269/4000000000000 : ℝ)*(sp1) + (723923742099299/25000000000000 : ℝ)*(sp2) + (1450378239370071/100000000000000 : ℝ)*(sp3) + (2408848033/12500000000000 : ℝ)*(sp4) + (7358201821/100000000000000 : ℝ)*(sp7) + (1450385597571891/100000000000000 : ℝ)*(f.failure) + (1447847753872753/50000000000000 : ℝ)*(f.sum) + (47247769790911/9128750000000000000000000000 : ℝ)*base66 + (20638725503712878857/3651500000000000000000000000000000 : ℝ)*base68 + (11811236657858378857/3651500000000000000000000000000000 : ℝ)*base70 + (8547005678317121143/3651500000000000000000000000000000 : ℝ)*base71 + (113051284149199/36515000000000000000000000000 : ℝ)*base74 + (22069114949916878857/3651500000000000000000000000000000 : ℝ)*base76 + (5021178240109621143/3651500000000000000000000000000000 : ℝ)*base77 + (28576553856541121143/3651500000000000000000000000000000 : ℝ)*base79 + (26805128433487/18257500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (106196379/10000000000000000000000 : ℝ)*base90 + (106196379/10000000000000000000000 : ℝ)*base92 + (106196379/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11972220469146045965517/4564375000000000000000000000 : ℝ) := by norm_num
    linear_combination (357196323/50000000000000 : ℝ)*(base19) + (85843201/10000000000000 : ℝ)*(base23) + (2261723/10000000000000 : ℝ)*(upper2) + (2842169/3125000000000 : ℝ)*(upper3) + (61421231/100000000000000 : ℝ)*(upper5) + (275395574115653/12500000000000 : ℝ)*(major0) + (275395574115653/12500000000000 : ℝ)*(major1) + (275395574115653/12500000000000 : ℝ)*(major2) + (3321283383/50000000000000 : ℝ)*(sp1) + (2223476747/25000000000000 : ℝ)*(sp2) + (2935837433427069/100000000000000 : ℝ)*(sp4) + (366978759558457/12500000000000 : ℝ)*(sp5) + (2935827681088071/100000000000000 : ℝ)*(sp6) + (367622916247757/25000000000000 : ℝ)*(sp7) + (367622916247757/25000000000000 : ℝ)*(f.failure) + (2935837433427069/100000000000000 : ℝ)*(f.sum) + (32178595692749/18257500000000000000000000000 : ℝ)*base66 + (2679283933279912711/912875000000000000000000000000000 : ℝ)*base68 + (3764390296875462289/912875000000000000000000000000000 : ℝ)*base69 + (4367921798520587289/912875000000000000000000000000000 : ℝ)*base71 + (50072334363627/9128750000000000000000000000 : ℝ)*base74 + (6878781480836087289/912875000000000000000000000000000 : ℝ)*base75 + (1350783176151787711/912875000000000000000000000000000 : ℝ)*base78 + (175948147544037711/912875000000000000000000000000000 : ℝ)*base80 + (40998250266967/36515000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3794533/2500000000000000000000 : ℝ)*base90 + (3794533/2500000000000000000000 : ℝ)*base92 + (3794533/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1160_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5089/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/400 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9151/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1160_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1160_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9151/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1160_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1160_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1160_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9151/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1160_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
