-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1176_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:47:44.461662+00:00
-- url     : https://prove2.me/submissions/014512c6-c21d-4653-a46b-80fc943c0358

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
theorem support_rectangle_w1176_s9_0 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1075368431/5000000000 : ℝ)*x 0 + (5392366439/10000000000 : ℝ)*x 1 + (5266318761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075368431/5000000000 : ℝ)^8369 ≤ (6536059297391/50000000000000 : ℝ)^6321 := by
    have hnat : (1075368431 : ℕ)^8369*50000000000000^6321 ≤ 6536059297391^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075368431 5000000000 6536059297391 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392366439/10000000000 : ℝ)^8369 ≤ (44144448087357/100000000000000 : ℝ)^6321 := by
    have hnat : (5392366439 : ℕ)^8369*100000000000000^6321 ≤ 44144448087357^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392366439 10000000000 44144448087357 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266318761/10000000000 : ℝ)^8369 ≤ (10695858326137/25000000000000 : ℝ)^6321 := by
    have hnat : (5266318761 : ℕ)^8369*25000000000000^6321 ≤ 10695858326137^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266318761 10000000000 10695858326137 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1075368431/5000000000 : ℝ), (5392366439/10000000000 : ℝ), (5266318761/10000000000 : ℝ)] ![(6536059297391/50000000000000 : ℝ), (44144448087357/100000000000000 : ℝ), (10695858326137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1075368431/5000000000 : ℝ)|^8369 ≤ (6536059297391/50000000000000 : ℝ)^6321
        have hw : |(-1075368431/5000000000 : ℝ)|=(1075368431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392366439/10000000000 : ℝ)|^8369 ≤ (44144448087357/100000000000000 : ℝ)^6321
        have hw : |(5392366439/10000000000 : ℝ)|=(5392366439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266318761/10000000000 : ℝ)|^8369 ≤ (10695858326137/25000000000000 : ℝ)^6321
        have hw : |(5266318761/10000000000 : ℝ)|=(5266318761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s9_1 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672305327/5000000000 : ℝ)*x 0 + (-44293227/200000000 : ℝ)*x 1 + (5266318717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672305327/5000000000 : ℝ)^8369 ≤ (43627572903749/100000000000000 : ℝ)^6321 := by
    have hnat : (2672305327 : ℕ)^8369*100000000000000^6321 ≤ 43627572903749^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672305327 5000000000 43627572903749 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44293227/200000000 : ℝ)^8369 ≤ (6794497119681/50000000000000 : ℝ)^6321 := by
    have hnat : (44293227 : ℕ)^8369*50000000000000^6321 ≤ 6794497119681^6321*200000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44293227 200000000 6794497119681 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266318717/10000000000 : ℝ)^8369 ≤ (21391716415639/50000000000000 : ℝ)^6321 := by
    have hnat : (5266318717 : ℕ)^8369*50000000000000^6321 ≤ 21391716415639^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266318717 10000000000 21391716415639 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672305327/5000000000 : ℝ), (-44293227/200000000 : ℝ), (5266318717/10000000000 : ℝ)] ![(43627572903749/100000000000000 : ℝ), (6794497119681/50000000000000 : ℝ), (21391716415639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672305327/5000000000 : ℝ)|^8369 ≤ (43627572903749/100000000000000 : ℝ)^6321
        have hw : |(2672305327/5000000000 : ℝ)|=(2672305327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44293227/200000000 : ℝ)|^8369 ≤ (6794497119681/50000000000000 : ℝ)^6321
        have hw : |(-44293227/200000000 : ℝ)|=(44293227/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266318717/10000000000 : ℝ)|^8369 ≤ (21391716415639/50000000000000 : ℝ)^6321
        have hw : |(5266318717/10000000000 : ℝ)|=(5266318717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s9_2 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672305303/5000000000 : ℝ)*x 0 + (2633159379/5000000000 : ℝ)*x 1 + (-2214661361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672305303/5000000000 : ℝ)^8369 ≤ (2181378619249/5000000000000 : ℝ)^6321 := by
    have hnat : (2672305303 : ℕ)^8369*5000000000000^6321 ≤ 2181378619249^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672305303 5000000000 2181378619249 5000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633159379/5000000000 : ℝ)^8369 ≤ (1069585831807/2500000000000 : ℝ)^6321 := by
    have hnat : (2633159379 : ℕ)^8369*2500000000000^6321 ≤ 1069585831807^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633159379 5000000000 1069585831807 2500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214661361/10000000000 : ℝ)^8369 ≤ (543559773149/4000000000000 : ℝ)^6321 := by
    have hnat : (2214661361 : ℕ)^8369*4000000000000^6321 ≤ 543559773149^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214661361 10000000000 543559773149 4000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672305303/5000000000 : ℝ), (2633159379/5000000000 : ℝ), (-2214661361/10000000000 : ℝ)] ![(2181378619249/5000000000000 : ℝ), (1069585831807/2500000000000 : ℝ), (543559773149/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672305303/5000000000 : ℝ)|^8369 ≤ (2181378619249/5000000000000 : ℝ)^6321
        have hw : |(2672305303/5000000000 : ℝ)|=(2672305303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633159379/5000000000 : ℝ)|^8369 ≤ (1069585831807/2500000000000 : ℝ)^6321
        have hw : |(2633159379/5000000000 : ℝ)|=(2633159379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2214661361/10000000000 : ℝ)|^8369 ≤ (543559773149/4000000000000 : ℝ)^6321
        have hw : |(-2214661361/10000000000 : ℝ)|=(2214661361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s9_3 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871981523/2000000000 : ℝ)*x 0 + (2117745139/5000000000 : ℝ)*x 1 + (4487932467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871981523/2000000000 : ℝ)^8369 ≤ (6663434783523/20000000000000 : ℝ)^6321 := by
    have hnat : (871981523 : ℕ)^8369*20000000000000^6321 ≤ 6663434783523^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871981523 2000000000 6663434783523 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117745139/5000000000 : ℝ)^8369 ≤ (32064223024287/100000000000000 : ℝ)^6321 := by
    have hnat : (2117745139 : ℕ)^8369*100000000000000^6321 ≤ 32064223024287^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117745139 5000000000 32064223024287 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487932467/10000000000 : ℝ)^8369 ≤ (3461860303699/10000000000000 : ℝ)^6321 := by
    have hnat : (4487932467 : ℕ)^8369*10000000000000^6321 ≤ 3461860303699^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487932467 10000000000 3461860303699 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871981523/2000000000 : ℝ), (2117745139/5000000000 : ℝ), (4487932467/10000000000 : ℝ)] ![(6663434783523/20000000000000 : ℝ), (32064223024287/100000000000000 : ℝ), (3461860303699/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871981523/2000000000 : ℝ)|^8369 ≤ (6663434783523/20000000000000 : ℝ)^6321
        have hw : |(871981523/2000000000 : ℝ)|=(871981523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117745139/5000000000 : ℝ)|^8369 ≤ (32064223024287/100000000000000 : ℝ)^6321
        have hw : |(2117745139/5000000000 : ℝ)|=(2117745139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487932467/10000000000 : ℝ)|^8369 ≤ (3461860303699/10000000000000 : ℝ)^6321
        have hw : |(4487932467/10000000000 : ℝ)|=(4487932467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s9_4 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-537685417/2500000000 : ℝ)*x 0 + (2633317773/5000000000 : ℝ)*x 1 + (2696024249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537685417/2500000000 : ℝ)^8369 ≤ (13072157269789/100000000000000 : ℝ)^6321 := by
    have hnat : (537685417 : ℕ)^8369*100000000000000^6321 ≤ 13072157269789^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537685417 2500000000 13072157269789 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633317773/5000000000 : ℝ)^8369 ≤ (42786840720163/100000000000000 : ℝ)^6321 := by
    have hnat : (2633317773 : ℕ)^8369*100000000000000^6321 ≤ 42786840720163^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633317773 5000000000 42786840720163 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696024249/5000000000 : ℝ)^8369 ≤ (22070500997711/50000000000000 : ℝ)^6321 := by
    have hnat : (2696024249 : ℕ)^8369*50000000000000^6321 ≤ 22070500997711^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696024249 5000000000 22070500997711 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537685417/2500000000 : ℝ), (2633317773/5000000000 : ℝ), (2696024249/5000000000 : ℝ)] ![(13072157269789/100000000000000 : ℝ), (42786840720163/100000000000000 : ℝ), (22070500997711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537685417/2500000000 : ℝ)|^8369 ≤ (13072157269789/100000000000000 : ℝ)^6321
        have hw : |(-537685417/2500000000 : ℝ)|=(537685417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633317773/5000000000 : ℝ)|^8369 ≤ (42786840720163/100000000000000 : ℝ)^6321
        have hw : |(2633317773/5000000000 : ℝ)|=(2633317773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696024249/5000000000 : ℝ)|^8369 ≤ (22070500997711/50000000000000 : ℝ)^6321
        have hw : |(2696024249/5000000000 : ℝ)|=(2696024249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s9_5 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359917233/10000000000 : ℝ)*x 0 + (35898383/80000000 : ℝ)*x 1 + (1059031787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359917233/10000000000 : ℝ)^8369 ≤ (16658635614491/50000000000000 : ℝ)^6321 := by
    have hnat : (4359917233 : ℕ)^8369*50000000000000^6321 ≤ 16658635614491^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359917233 10000000000 16658635614491 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35898383/80000000 : ℝ)^8369 ≤ (34612122132111/100000000000000 : ℝ)^6321 := by
    have hnat : (35898383 : ℕ)^8369*100000000000000^6321 ≤ 34612122132111^6321*80000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35898383 80000000 34612122132111 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059031787/2500000000 : ℝ)^8369 ≤ (3207060663183/10000000000000 : ℝ)^6321 := by
    have hnat : (1059031787 : ℕ)^8369*10000000000000^6321 ≤ 3207060663183^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059031787 2500000000 3207060663183 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359917233/10000000000 : ℝ), (35898383/80000000 : ℝ), (1059031787/2500000000 : ℝ)] ![(16658635614491/50000000000000 : ℝ), (34612122132111/100000000000000 : ℝ), (3207060663183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359917233/10000000000 : ℝ)|^8369 ≤ (16658635614491/50000000000000 : ℝ)^6321
        have hw : |(4359917233/10000000000 : ℝ)|=(4359917233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35898383/80000000 : ℝ)|^8369 ≤ (34612122132111/100000000000000 : ℝ)^6321
        have hw : |(35898383/80000000 : ℝ)|=(35898383/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1059031787/2500000000 : ℝ)|^8369 ≤ (3207060663183/10000000000000 : ℝ)^6321
        have hw : |(1059031787/2500000000 : ℝ)|=(1059031787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1176_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5699/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3517/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11397/100000 : ℝ) ^ (523/128 : ℝ) ≤ (6999630827359399/50000000000000000000 : ℝ) := by
    have hpowers : (11397/100000 : ℝ)^523 ≤ (6999630827359399/50000000000000000000 : ℝ)^128 := by
      have hnat : (11397 : ℕ)^523*50000000000000000000^128 ≤ 6999630827359399^128*100000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11397 100000 6999630827359399 50000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11397/100000 : ℝ)) (X := (6999630827359399/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3517/25000 : ℝ) ^ (523/128 : ℝ) ≤ (33092582252755669/100000000000000000000 : ℝ) := by
    have hpowers : (3517/25000 : ℝ)^523 ≤ (33092582252755669/100000000000000000000 : ℝ)^128 := by
      have hnat : (3517 : ℕ)^523*100000000000000000000^128 ≤ 33092582252755669^128*25000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3517 25000 33092582252755669 100000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3517/25000 : ℝ)) (X := (33092582252755669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006999630827359399/25000000000000000000 : ℝ) ≤ (1250085646083349/1250000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (25006999630827359399/25000000000000000000 : ℝ)^128 ≤ (1250085646083349/1250000000000000 : ℝ)^523 := by
      have hnat : (25006999630827359399 : ℕ)^128*1250000000000000^523 ≤ 1250085646083349^523*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006999630827359399 25000000000000000000 1250085646083349 1250000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250085646083349/1250000000000000 : ℝ)) (X := (25006999630827359399/25000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047091843907474467/100000000000000000000 : ℝ) ≤ (62507202060689/62500000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (100047091843907474467/100000000000000000000 : ℝ)^128 ≤ (62507202060689/62500000000000 : ℝ)^523 := by
      have hnat : (100047091843907474467 : ℕ)^128*62500000000000^523 ≤ 62507202060689^523*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047091843907474467 100000000000000000000 62507202060689 62500000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62507202060689/62500000000000 : ℝ)) (X := (100047091843907474467/100000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033092582252755669/50000000000000000000 : ℝ) ≤ (1250202436344211/1250000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (50033092582252755669/50000000000000000000 : ℝ)^128 ≤ (1250202436344211/1250000000000000 : ℝ)^523 := by
      have hnat : (50033092582252755669 : ℕ)^128*1250000000000000^523 ≤ 1250202436344211^523*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033092582252755669 50000000000000000000 1250202436344211 1250000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250202436344211/1250000000000000 : ℝ)) (X := (50033092582252755669/50000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6999630827359399/50000000000000000000 : ℝ) ≤ ((667529540417116193/667750000000000000 : ℝ)+2*(58395130431/33387500000000 : ℝ)*(11397/100000 : ℝ))^(523/128 : ℝ) := by
    rw [show (667529540417116193/667750000000000000 : ℝ)+2*(58395130431/33387500000000 : ℝ)*(11397/100000 : ℝ)=(1250085646083349/1250000000000000 : ℝ) by norm_num, show 1+2*(6999630827359399/50000000000000000000 : ℝ)=(25006999630827359399/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33092582252755669/100000000000000000000 : ℝ)+(6999630827359399/50000000000000000000 : ℝ) ≤ ((667529540417116193/667750000000000000 : ℝ)+(58395130431/33387500000000 : ℝ)*((3517/25000 : ℝ)+(11397/100000 : ℝ)))^(523/128 : ℝ) := by
    rw [show (667529540417116193/667750000000000000 : ℝ)+(58395130431/33387500000000 : ℝ)*((3517/25000 : ℝ)+(11397/100000 : ℝ))=(62507202060689/62500000000000 : ℝ) by norm_num, show 1+(33092582252755669/100000000000000000000 : ℝ)+(6999630827359399/50000000000000000000 : ℝ)=(100047091843907474467/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33092582252755669/100000000000000000000 : ℝ) ≤ ((667529540417116193/667750000000000000 : ℝ)+2*(58395130431/33387500000000 : ℝ)*(3517/25000 : ℝ))^(523/128 : ℝ) := by
    rw [show (667529540417116193/667750000000000000 : ℝ)+2*(58395130431/33387500000000 : ℝ)*(3517/25000 : ℝ)=(1250202436344211/1250000000000000 : ℝ) by norm_num, show 1+2*(33092582252755669/100000000000000000000 : ℝ)=(50033092582252755669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (667529540417116193/667750000000000000 : ℝ)*(X 1 0+X 2 0)+(58395130431/33387500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (667529540417116193/667750000000000000 : ℝ)) (alpha := (58395130431/33387500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (667529540417116193/667750000000000000 : ℝ)*(X 0 1+X 2 1)+(58395130431/33387500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (667529540417116193/667750000000000000 : ℝ)) (alpha := (58395130431/33387500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (667529540417116193/667750000000000000 : ℝ)*(X 0 2+X 1 2)+(58395130431/33387500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (667529540417116193/667750000000000000 : ℝ)) (alpha := (58395130431/33387500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1075368431/5000000000 : ℝ)*X 0 0+(5392366439/10000000000 : ℝ)*X 0 1+(5266318761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672305327/5000000000 : ℝ)*X 1 0+(-44293227/200000000 : ℝ)*X 1 1+(5266318717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672305303/5000000000 : ℝ)*X 2 0+(2633159379/5000000000 : ℝ)*X 2 1+(-2214661361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871981523/2000000000 : ℝ)*X 0 0+(2117745139/5000000000 : ℝ)*X 0 1+(4487932467/10000000000 : ℝ)*X 0 2+(871981523/2000000000 : ℝ)*X 1 0+(2117745139/5000000000 : ℝ)*X 1 1+(4487932467/10000000000 : ℝ)*X 1 2+(871981523/2000000000 : ℝ)*X 2 0+(2117745139/5000000000 : ℝ)*X 2 1+(4487932467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-537685417/2500000000 : ℝ)*X 0 0+(2633317773/5000000000 : ℝ)*X 0 1+(2696024249/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4359917233/10000000000 : ℝ)*X 0 0+(35898383/80000000 : ℝ)*X 0 1+(1059031787/2500000000 : ℝ)*X 0 2+(4359917233/10000000000 : ℝ)*X 1 0+(35898383/80000000 : ℝ)*X 1 1+(1059031787/2500000000 : ℝ)*X 1 2+(4359917233/10000000000 : ℝ)*X 2 0+(35898383/80000000 : ℝ)*X 2 1+(1059031787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11702651375316787987948203/3338750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (728584827/100000000000000 : ℝ)*(base19) + (60802481/10000000000000 : ℝ)*(base23) + (13176817/50000000000000 : ℝ)*(lower2) + (25124101/25000000000000 : ℝ)*(upper3) + (17102761/50000000000000 : ℝ)*(upper5) + (594743311745369/10000000000000 : ℝ)*(major0) + (594743311745369/10000000000000 : ℝ)*(major1) + (594743311745369/10000000000000 : ℝ)*(major2) + (3966762906420439/50000000000000 : ℝ)*(sp0) + (495846359110967/6250000000000 : ℝ)*(sp1) + (7933541866335489/100000000000000 : ℝ)*(sp2) + (990328170431983/25000000000000 : ℝ)*(sp3) + (16661519421/100000000000000 : ℝ)*(sp4) + (2192396497/20000000000000 : ℝ)*(sp5) + (247582727731901/6250000000000 : ℝ)*(f.failure) + (7933542474360299/100000000000000 : ℝ)*(f.sum) + (4413310715567/2671000000000000000000000000 : ℝ)*base66 + (2184288008332283/6677500000000000000000000000000 : ℝ)*base68 + (173149429380659783/6677500000000000000000000000000 : ℝ)*base70 + (29989051406017283/6677500000000000000000000000000 : ℝ)*base72 + (18432508686217/2671000000000000000000000000 : ℝ)*base74 + (139448872208079783/6677500000000000000000000000000 : ℝ)*base76 + (41477807987182283/6677500000000000000000000000000 : ℝ)*base78 + (106749733547167283/6677500000000000000000000000000 : ℝ)*base80 + (15234983067521/2671000000000000000000000000 : ℝ)*base82 + (6257421/625000000000000000000 : ℝ)*base89 + (6257421/625000000000000000000 : ℝ)*base91 + (6257421/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1176_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1176_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1176_box_0 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2024950927/10000000000 : ℝ)*x 0 + (2687910091/5000000000 : ℝ)*x 1 + (2687910143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2024950927/10000000000 : ℝ)^8369 ≤ (12069610100273/100000000000000 : ℝ)^6321 := by
    have hnat : (2024950927 : ℕ)^8369*100000000000000^6321 ≤ 12069610100273^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024950927 10000000000 12069610100273 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687910091/5000000000 : ℝ)^8369 ≤ (5495649297267/12500000000000 : ℝ)^6321 := by
    have hnat : (2687910091 : ℕ)^8369*12500000000000^6321 ≤ 5495649297267^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687910091 5000000000 5495649297267 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687910143/5000000000 : ℝ)^8369 ≤ (21982597752129/50000000000000 : ℝ)^6321 := by
    have hnat : (2687910143 : ℕ)^8369*50000000000000^6321 ≤ 21982597752129^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687910143 5000000000 21982597752129 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2024950927/10000000000 : ℝ), (2687910091/5000000000 : ℝ), (2687910143/5000000000 : ℝ)] ![(12069610100273/100000000000000 : ℝ), (5495649297267/12500000000000 : ℝ), (21982597752129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2024950927/10000000000 : ℝ)|^8369 ≤ (12069610100273/100000000000000 : ℝ)^6321
        have hw : |(-2024950927/10000000000 : ℝ)|=(2024950927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687910091/5000000000 : ℝ)|^8369 ≤ (5495649297267/12500000000000 : ℝ)^6321
        have hw : |(2687910091/5000000000 : ℝ)|=(2687910091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687910143/5000000000 : ℝ)|^8369 ≤ (21982597752129/50000000000000 : ℝ)^6321
        have hw : |(2687910143/5000000000 : ℝ)|=(2687910143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_1 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296287979/10000000000 : ℝ)*x 0 + (-2132893227/10000000000 : ℝ)*x 1 + (5375820407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296287979/10000000000 : ℝ)^8369 ≤ (43106083072793/100000000000000 : ℝ)^6321 := by
    have hnat : (5296287979 : ℕ)^8369*100000000000000^6321 ≤ 43106083072793^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296287979 10000000000 43106083072793 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132893227/10000000000 : ℝ)^8369 ≤ (12928720093127/100000000000000 : ℝ)^6321 := by
    have hnat : (2132893227 : ℕ)^8369*100000000000000^6321 ≤ 12928720093127^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132893227 10000000000 12928720093127 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375820407/10000000000 : ℝ)^8369 ≤ (43965196814457/100000000000000 : ℝ)^6321 := by
    have hnat : (5375820407 : ℕ)^8369*100000000000000^6321 ≤ 43965196814457^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375820407 10000000000 43965196814457 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296287979/10000000000 : ℝ), (-2132893227/10000000000 : ℝ), (5375820407/10000000000 : ℝ)] ![(43106083072793/100000000000000 : ℝ), (12928720093127/100000000000000 : ℝ), (43965196814457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296287979/10000000000 : ℝ)|^8369 ≤ (43106083072793/100000000000000 : ℝ)^6321
        have hw : |(5296287979/10000000000 : ℝ)|=(5296287979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2132893227/10000000000 : ℝ)|^8369 ≤ (12928720093127/100000000000000 : ℝ)^6321
        have hw : |(-2132893227/10000000000 : ℝ)|=(2132893227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375820407/10000000000 : ℝ)|^8369 ≤ (43965196814457/100000000000000 : ℝ)^6321
        have hw : |(5375820407/10000000000 : ℝ)|=(5375820407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_2 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (662035957/1250000000 : ℝ)*x 0 + (2687910299/5000000000 : ℝ)*x 1 + (-533223351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662035957/1250000000 : ℝ)^8369 ≤ (5388259949021/12500000000000 : ℝ)^6321 := by
    have hnat : (662035957 : ℕ)^8369*12500000000000^6321 ≤ 5388259949021^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662035957 1250000000 5388259949021 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687910299/5000000000 : ℝ)^8369 ≤ (686956232541/1562500000000 : ℝ)^6321 := by
    have hnat : (2687910299 : ℕ)^8369*1562500000000^6321 ≤ 686956232541^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687910299 5000000000 686956232541 1562500000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533223351/2500000000 : ℝ)^8369 ≤ (12928721513647/100000000000000 : ℝ)^6321 := by
    have hnat : (533223351 : ℕ)^8369*100000000000000^6321 ≤ 12928721513647^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533223351 2500000000 12928721513647 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662035957/1250000000 : ℝ), (2687910299/5000000000 : ℝ), (-533223351/2500000000 : ℝ)] ![(5388259949021/12500000000000 : ℝ), (686956232541/1562500000000 : ℝ), (12928721513647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662035957/1250000000 : ℝ)|^8369 ≤ (5388259949021/12500000000000 : ℝ)^6321
        have hw : |(662035957/1250000000 : ℝ)|=(662035957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687910299/5000000000 : ℝ)|^8369 ≤ (686956232541/1562500000000 : ℝ)^6321
        have hw : |(2687910299/5000000000 : ℝ)|=(2687910299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-533223351/2500000000 : ℝ)|^8369 ≤ (12928721513647/100000000000000 : ℝ)^6321
        have hw : |(-533223351/2500000000 : ℝ)|=(533223351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_3 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2233547111/5000000000 : ℝ)*x 0 + (4308398919/10000000000 : ℝ)*x 1 + (1077099731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2233547111/5000000000 : ℝ)^8369 ≤ (8601485857819/25000000000000 : ℝ)^6321 := by
    have hnat : (2233547111 : ℕ)^8369*25000000000000^6321 ≤ 8601485857819^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233547111 5000000000 8601485857819 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4308398919/10000000000 : ℝ)^8369 ≤ (3279702825091/10000000000000 : ℝ)^6321 := by
    have hnat : (4308398919 : ℕ)^8369*10000000000000^6321 ≤ 3279702825091^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308398919 10000000000 3279702825091 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077099731/2500000000 : ℝ)^8369 ≤ (4099628537663/12500000000000 : ℝ)^6321 := by
    have hnat : (1077099731 : ℕ)^8369*12500000000000^6321 ≤ 4099628537663^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077099731 2500000000 4099628537663 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2233547111/5000000000 : ℝ), (4308398919/10000000000 : ℝ), (1077099731/2500000000 : ℝ)] ![(8601485857819/25000000000000 : ℝ), (3279702825091/10000000000000 : ℝ), (4099628537663/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2233547111/5000000000 : ℝ)|^8369 ≤ (8601485857819/25000000000000 : ℝ)^6321
        have hw : |(2233547111/5000000000 : ℝ)|=(2233547111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4308398919/10000000000 : ℝ)|^8369 ≤ (3279702825091/10000000000000 : ℝ)^6321
        have hw : |(4308398919/10000000000 : ℝ)|=(4308398919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077099731/2500000000 : ℝ)|^8369 ≤ (4099628537663/12500000000000 : ℝ)^6321
        have hw : |(1077099731/2500000000 : ℝ)|=(1077099731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_4 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-569474863/2500000000 : ℝ)*x 0 + (5281560269/10000000000 : ℝ)*x 1 + (5281560353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (569474863/2500000000 : ℝ)^8369 ≤ (7052549698353/50000000000000 : ℝ)^6321 := by
    have hnat : (569474863 : ℕ)^8369*50000000000000^6321 ≤ 7052549698353^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569474863 2500000000 7052549698353 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281560269/10000000000 : ℝ)^8369 ≤ (42947449844359/100000000000000 : ℝ)^6321 := by
    have hnat : (5281560269 : ℕ)^8369*100000000000000^6321 ≤ 42947449844359^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281560269 10000000000 42947449844359 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281560353/10000000000 : ℝ)^8369 ≤ (42947450748721/100000000000000 : ℝ)^6321 := by
    have hnat : (5281560353 : ℕ)^8369*100000000000000^6321 ≤ 42947450748721^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281560353 10000000000 42947450748721 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-569474863/2500000000 : ℝ), (5281560269/10000000000 : ℝ), (5281560353/10000000000 : ℝ)] ![(7052549698353/50000000000000 : ℝ), (42947449844359/100000000000000 : ℝ), (42947450748721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-569474863/2500000000 : ℝ)|^8369 ≤ (7052549698353/50000000000000 : ℝ)^6321
        have hw : |(-569474863/2500000000 : ℝ)|=(569474863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281560269/10000000000 : ℝ)|^8369 ≤ (42947449844359/100000000000000 : ℝ)^6321
        have hw : |(5281560269/10000000000 : ℝ)|=(5281560269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281560353/10000000000 : ℝ)|^8369 ≤ (42947450748721/100000000000000 : ℝ)^6321
        have hw : |(5281560353/10000000000 : ℝ)|=(5281560353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_5 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681415921/5000000000 : ℝ)*x 0 + (-2170072047/10000000000 : ℝ)*x 1 + (5281560289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681415921/5000000000 : ℝ)^8369 ≤ (21912305240087/50000000000000 : ℝ)^6321 := by
    have hnat : (2681415921 : ℕ)^8369*50000000000000^6321 ≤ 21912305240087^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681415921 5000000000 21912305240087 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170072047/10000000000 : ℝ)^8369 ≤ (3306984861611/25000000000000 : ℝ)^6321 := by
    have hnat : (2170072047 : ℕ)^8369*25000000000000^6321 ≤ 3306984861611^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170072047 10000000000 3306984861611 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281560289/10000000000 : ℝ)^8369 ≤ (42947450059683/100000000000000 : ℝ)^6321 := by
    have hnat : (5281560289 : ℕ)^8369*100000000000000^6321 ≤ 42947450059683^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281560289 10000000000 42947450059683 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681415921/5000000000 : ℝ), (-2170072047/10000000000 : ℝ), (5281560289/10000000000 : ℝ)] ![(21912305240087/50000000000000 : ℝ), (3306984861611/25000000000000 : ℝ), (42947450059683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681415921/5000000000 : ℝ)|^8369 ≤ (21912305240087/50000000000000 : ℝ)^6321
        have hw : |(2681415921/5000000000 : ℝ)|=(2681415921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170072047/10000000000 : ℝ)|^8369 ≤ (3306984861611/25000000000000 : ℝ)^6321
        have hw : |(-2170072047/10000000000 : ℝ)|=(2170072047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281560289/10000000000 : ℝ)|^8369 ≤ (42947450059683/100000000000000 : ℝ)^6321
        have hw : |(5281560289/10000000000 : ℝ)|=(5281560289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_6 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536283181/1000000000 : ℝ)*x 0 + (1056312063/2000000000 : ℝ)*x 1 + (-434014411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536283181/1000000000 : ℝ)^8369 ≤ (43824610133947/100000000000000 : ℝ)^6321 := by
    have hnat : (536283181 : ℕ)^8369*100000000000000^6321 ≤ 43824610133947^6321*1000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536283181 1000000000 43824610133947 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056312063/2000000000 : ℝ)^8369 ≤ (8589490067921/20000000000000 : ℝ)^6321 := by
    have hnat : (1056312063 : ℕ)^8369*20000000000000^6321 ≤ 8589490067921^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056312063 2000000000 8589490067921 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434014411/2000000000 : ℝ)^8369 ≤ (13227939511009/100000000000000 : ℝ)^6321 := by
    have hnat : (434014411 : ℕ)^8369*100000000000000^6321 ≤ 13227939511009^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434014411 2000000000 13227939511009 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536283181/1000000000 : ℝ), (1056312063/2000000000 : ℝ), (-434014411/2000000000 : ℝ)] ![(43824610133947/100000000000000 : ℝ), (8589490067921/20000000000000 : ℝ), (13227939511009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536283181/1000000000 : ℝ)|^8369 ≤ (43824610133947/100000000000000 : ℝ)^6321
        have hw : |(536283181/1000000000 : ℝ)|=(536283181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056312063/2000000000 : ℝ)|^8369 ≤ (8589490067921/20000000000000 : ℝ)^6321
        have hw : |(1056312063/2000000000 : ℝ)|=(1056312063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434014411/2000000000 : ℝ)|^8369 ≤ (13227939511009/100000000000000 : ℝ)^6321
        have hw : |(-434014411/2000000000 : ℝ)|=(434014411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_7 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2126172671/5000000000 : ℝ)*x 0 + (4415752791/10000000000 : ℝ)*x 1 + (551969097/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126172671/5000000000 : ℝ)^8369 ≤ (16116636449451/50000000000000 : ℝ)^6321 := by
    have hnat : (2126172671 : ℕ)^8369*50000000000000^6321 ≤ 16116636449451^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126172671 5000000000 16116636449451 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4415752791/10000000000 : ℝ)^8369 ≤ (5421338179/16000000000 : ℝ)^6321 := by
    have hnat : (4415752791 : ℕ)^8369*16000000000^6321 ≤ 5421338179^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415752791 10000000000 5421338179 16000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551969097/1250000000 : ℝ)^8369 ≤ (33883363466359/100000000000000 : ℝ)^6321 := by
    have hnat : (551969097 : ℕ)^8369*100000000000000^6321 ≤ 33883363466359^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551969097 1250000000 33883363466359 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126172671/5000000000 : ℝ), (4415752791/10000000000 : ℝ), (551969097/1250000000 : ℝ)] ![(16116636449451/50000000000000 : ℝ), (5421338179/16000000000 : ℝ), (33883363466359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126172671/5000000000 : ℝ)|^8369 ≤ (16116636449451/50000000000000 : ℝ)^6321
        have hw : |(2126172671/5000000000 : ℝ)|=(2126172671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4415752791/10000000000 : ℝ)|^8369 ≤ (5421338179/16000000000 : ℝ)^6321
        have hw : |(4415752791/10000000000 : ℝ)|=(4415752791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551969097/1250000000 : ℝ)|^8369 ≤ (33883363466359/100000000000000 : ℝ)^6321
        have hw : |(551969097/1250000000 : ℝ)|=(551969097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_8 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2224965629/10000000000 : ℝ)*x 0 + (5217389347/10000000000 : ℝ)*x 1 + (269271569/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2224965629/10000000000 : ℝ)^8369 ≤ (13672768818843/100000000000000 : ℝ)^6321 := by
    have hnat : (2224965629 : ℕ)^8369*100000000000000^6321 ≤ 13672768818843^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224965629 10000000000 13672768818843 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217389347/10000000000 : ℝ)^8369 ≤ (42257935700933/100000000000000 : ℝ)^6321 := by
    have hnat : (5217389347 : ℕ)^8369*100000000000000^6321 ≤ 42257935700933^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217389347 10000000000 42257935700933 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269271569/500000000 : ℝ)^8369 ≤ (44069295469567/100000000000000 : ℝ)^6321 := by
    have hnat : (269271569 : ℕ)^8369*100000000000000^6321 ≤ 44069295469567^6321*500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269271569 500000000 44069295469567 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2224965629/10000000000 : ℝ), (5217389347/10000000000 : ℝ), (269271569/500000000 : ℝ)] ![(13672768818843/100000000000000 : ℝ), (42257935700933/100000000000000 : ℝ), (44069295469567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2224965629/10000000000 : ℝ)|^8369 ≤ (13672768818843/100000000000000 : ℝ)^6321
        have hw : |(-2224965629/10000000000 : ℝ)|=(2224965629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217389347/10000000000 : ℝ)|^8369 ≤ (42257935700933/100000000000000 : ℝ)^6321
        have hw : |(5217389347/10000000000 : ℝ)|=(5217389347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269271569/500000000 : ℝ)|^8369 ≤ (44069295469567/100000000000000 : ℝ)^6321
        have hw : |(269271569/500000000 : ℝ)|=(269271569/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_9 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289499977/10000000000 : ℝ)*x 0 + (-2129034041/10000000000 : ℝ)*x 1 + (215417241/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289499977/10000000000 : ℝ)^8369 ≤ (8606590246487/20000000000000 : ℝ)^6321 := by
    have hnat : (5289499977 : ℕ)^8369*20000000000000^6321 ≤ 8606590246487^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289499977 10000000000 8606590246487 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2129034041/10000000000 : ℝ)^8369 ≤ (12897757128511/100000000000000 : ℝ)^6321 := by
    have hnat : (2129034041 : ℕ)^8369*100000000000000^6321 ≤ 12897757128511^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129034041 10000000000 12897757128511 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215417241/400000000 : ℝ)^8369 ≤ (5508661452921/12500000000000 : ℝ)^6321 := by
    have hnat : (215417241 : ℕ)^8369*12500000000000^6321 ≤ 5508661452921^6321*400000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215417241 400000000 5508661452921 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289499977/10000000000 : ℝ), (-2129034041/10000000000 : ℝ), (215417241/400000000 : ℝ)] ![(8606590246487/20000000000000 : ℝ), (12897757128511/100000000000000 : ℝ), (5508661452921/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289499977/10000000000 : ℝ)|^8369 ≤ (8606590246487/20000000000000 : ℝ)^6321
        have hw : |(5289499977/10000000000 : ℝ)|=(5289499977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2129034041/10000000000 : ℝ)|^8369 ≤ (12897757128511/100000000000000 : ℝ)^6321
        have hw : |(-2129034041/10000000000 : ℝ)|=(2129034041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215417241/400000000 : ℝ)|^8369 ≤ (5508661452921/12500000000000 : ℝ)^6321
        have hw : |(215417241/400000000 : ℝ)|=(215417241/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_10 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289499871/10000000000 : ℝ)*x 0 + (5385430811/10000000000 : ℝ)*x 1 + (-2129034473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289499871/10000000000 : ℝ)^8369 ≤ (43032950090661/100000000000000 : ℝ)^6321 := by
    have hnat : (5289499871 : ℕ)^8369*100000000000000^6321 ≤ 43032950090661^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289499871 10000000000 43032950090661 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385430811/10000000000 : ℝ)^8369 ≤ (8813857860963/20000000000000 : ℝ)^6321 := by
    have hnat : (5385430811 : ℕ)^8369*20000000000000^6321 ≤ 8813857860963^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385430811 10000000000 8813857860963 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129034473/10000000000 : ℝ)^8369 ≤ (1289776059351/10000000000000 : ℝ)^6321 := by
    have hnat : (2129034473 : ℕ)^8369*10000000000000^6321 ≤ 1289776059351^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129034473 10000000000 1289776059351 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289499871/10000000000 : ℝ), (5385430811/10000000000 : ℝ), (-2129034473/10000000000 : ℝ)] ![(43032950090661/100000000000000 : ℝ), (8813857860963/20000000000000 : ℝ), (1289776059351/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289499871/10000000000 : ℝ)|^8369 ≤ (43032950090661/100000000000000 : ℝ)^6321
        have hw : |(5289499871/10000000000 : ℝ)|=(5289499871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385430811/10000000000 : ℝ)|^8369 ≤ (8813857860963/20000000000000 : ℝ)^6321
        have hw : |(5385430811/10000000000 : ℝ)|=(5385430811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2129034473/10000000000 : ℝ)|^8369 ≤ (1289776059351/10000000000000 : ℝ)^6321
        have hw : |(-2129034473/10000000000 : ℝ)|=(2129034473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_11 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4488717349/10000000000 : ℝ)*x 0 + (2148723401/5000000000 : ℝ)*x 1 + (859489369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4488717349/10000000000 : ℝ)^8369 ≤ (34626619220971/100000000000000 : ℝ)^6321 := by
    have hnat : (4488717349 : ℕ)^8369*100000000000000^6321 ≤ 34626619220971^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488717349 10000000000 34626619220971 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148723401/5000000000 : ℝ)^8369 ≤ (32686690163451/100000000000000 : ℝ)^6321 := by
    have hnat : (2148723401 : ℕ)^8369*100000000000000^6321 ≤ 32686690163451^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148723401 5000000000 32686690163451 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (859489369/2000000000 : ℝ)^8369 ≤ (51072954057/156250000000 : ℝ)^6321 := by
    have hnat : (859489369 : ℕ)^8369*156250000000^6321 ≤ 51072954057^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859489369 2000000000 51072954057 156250000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4488717349/10000000000 : ℝ), (2148723401/5000000000 : ℝ), (859489369/2000000000 : ℝ)] ![(34626619220971/100000000000000 : ℝ), (32686690163451/100000000000000 : ℝ), (51072954057/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4488717349/10000000000 : ℝ)|^8369 ≤ (34626619220971/100000000000000 : ℝ)^6321
        have hw : |(4488717349/10000000000 : ℝ)|=(4488717349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2148723401/5000000000 : ℝ)|^8369 ≤ (32686690163451/100000000000000 : ℝ)^6321
        have hw : |(2148723401/5000000000 : ℝ)|=(2148723401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(859489369/2000000000 : ℝ)|^8369 ≤ (51072954057/156250000000 : ℝ)^6321
        have hw : |(859489369/2000000000 : ℝ)|=(859489369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_12 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2078183247/10000000000 : ℝ)*x 0 + (5438737557/10000000000 : ℝ)*x 1 + (5273506601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078183247/10000000000 : ℝ)^8369 ≤ (1561434778183/12500000000000 : ℝ)^6321 := by
    have hnat : (2078183247 : ℕ)^8369*12500000000000^6321 ≤ 1561434778183^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078183247 10000000000 1561434778183 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438737557/10000000000 : ℝ)^8369 ≤ (11161939495067/25000000000000 : ℝ)^6321 := by
    have hnat : (5438737557 : ℕ)^8369*25000000000000^6321 ≤ 11161939495067^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438737557 10000000000 11161939495067 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273506601/10000000000 : ℝ)^8369 ≤ (8572152755107/20000000000000 : ℝ)^6321 := by
    have hnat : (5273506601 : ℕ)^8369*20000000000000^6321 ≤ 8572152755107^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273506601 10000000000 8572152755107 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2078183247/10000000000 : ℝ), (5438737557/10000000000 : ℝ), (5273506601/10000000000 : ℝ)] ![(1561434778183/12500000000000 : ℝ), (11161939495067/25000000000000 : ℝ), (8572152755107/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2078183247/10000000000 : ℝ)|^8369 ≤ (1561434778183/12500000000000 : ℝ)^6321
        have hw : |(-2078183247/10000000000 : ℝ)|=(2078183247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438737557/10000000000 : ℝ)|^8369 ≤ (11161939495067/25000000000000 : ℝ)^6321
        have hw : |(5438737557/10000000000 : ℝ)|=(5438737557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273506601/10000000000 : ℝ)|^8369 ≤ (8572152755107/20000000000000 : ℝ)^6321
        have hw : |(5273506601/10000000000 : ℝ)|=(5273506601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_13 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368515251/10000000000 : ℝ)*x 0 + (-27164901/125000000 : ℝ)*x 1 + (5273506327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368515251/10000000000 : ℝ)^8369 ≤ (43886113311689/100000000000000 : ℝ)^6321 := by
    have hnat : (5368515251 : ℕ)^8369*100000000000000^6321 ≤ 43886113311689^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368515251 10000000000 43886113311689 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27164901/125000000 : ℝ)^8369 ≤ (2650625169563/20000000000000 : ℝ)^6321 := by
    have hnat : (27164901 : ℕ)^8369*20000000000000^6321 ≤ 2650625169563^6321*125000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27164901 125000000 2650625169563 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273506327/10000000000 : ℝ)^8369 ≤ (42860760827051/100000000000000 : ℝ)^6321 := by
    have hnat : (5273506327 : ℕ)^8369*100000000000000^6321 ≤ 42860760827051^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273506327 10000000000 42860760827051 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368515251/10000000000 : ℝ), (-27164901/125000000 : ℝ), (5273506327/10000000000 : ℝ)] ![(43886113311689/100000000000000 : ℝ), (2650625169563/20000000000000 : ℝ), (42860760827051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368515251/10000000000 : ℝ)|^8369 ≤ (43886113311689/100000000000000 : ℝ)^6321
        have hw : |(5368515251/10000000000 : ℝ)|=(5368515251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27164901/125000000 : ℝ)|^8369 ≤ (2650625169563/20000000000000 : ℝ)^6321
        have hw : |(-27164901/125000000 : ℝ)|=(27164901/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273506327/10000000000 : ℝ)|^8369 ≤ (42860760827051/100000000000000 : ℝ)^6321
        have hw : |(5273506327/10000000000 : ℝ)|=(5273506327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_14 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368515299/10000000000 : ℝ)*x 0 + (2636753433/5000000000 : ℝ)*x 1 + (-1086595649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368515299/10000000000 : ℝ)^8369 ≤ (5485764228901/12500000000000 : ℝ)^6321 := by
    have hnat : (5368515299 : ℕ)^8369*12500000000000^6321 ≤ 5485764228901^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368515299 10000000000 5485764228901 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636753433/5000000000 : ℝ)^8369 ≤ (4286076662717/10000000000000 : ℝ)^6321 := by
    have hnat : (2636753433 : ℕ)^8369*10000000000000^6321 ≤ 4286076662717^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636753433 5000000000 4286076662717 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086595649/5000000000 : ℝ)^8369 ≤ (3313279883417/25000000000000 : ℝ)^6321 := by
    have hnat : (1086595649 : ℕ)^8369*25000000000000^6321 ≤ 3313279883417^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086595649 5000000000 3313279883417 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368515299/10000000000 : ℝ), (2636753433/5000000000 : ℝ), (-1086595649/5000000000 : ℝ)] ![(5485764228901/12500000000000 : ℝ), (4286076662717/10000000000000 : ℝ), (3313279883417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368515299/10000000000 : ℝ)|^8369 ≤ (5485764228901/12500000000000 : ℝ)^6321
        have hw : |(5368515299/10000000000 : ℝ)|=(5368515299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636753433/5000000000 : ℝ)|^8369 ≤ (4286076662717/10000000000000 : ℝ)^6321
        have hw : |(2636753433/5000000000 : ℝ)|=(2636753433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1086595649/5000000000 : ℝ)|^8369 ≤ (3313279883417/25000000000000 : ℝ)^6321
        have hw : |(-1086595649/5000000000 : ℝ)|=(1086595649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_box_15 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4233766167/10000000000 : ℝ)*x 0 + (884983983/2000000000 : ℝ)*x 1 + (884984011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4233766167/10000000000 : ℝ)^8369 ≤ (32046943117759/100000000000000 : ℝ)^6321 := by
    have hnat : (4233766167 : ℕ)^8369*100000000000000^6321 ≤ 32046943117759^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233766167 10000000000 32046943117759 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884983983/2000000000 : ℝ)^8369 ≤ (3397652772317/10000000000000 : ℝ)^6321 := by
    have hnat : (884983983 : ℕ)^8369*10000000000000^6321 ≤ 3397652772317^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884983983 2000000000 3397652772317 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884984011/2000000000 : ℝ)^8369 ≤ (16988264573223/50000000000000 : ℝ)^6321 := by
    have hnat : (884984011 : ℕ)^8369*50000000000000^6321 ≤ 16988264573223^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884984011 2000000000 16988264573223 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4233766167/10000000000 : ℝ), (884983983/2000000000 : ℝ), (884984011/2000000000 : ℝ)] ![(32046943117759/100000000000000 : ℝ), (3397652772317/10000000000000 : ℝ), (16988264573223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4233766167/10000000000 : ℝ)|^8369 ≤ (32046943117759/100000000000000 : ℝ)^6321
        have hw : |(4233766167/10000000000 : ℝ)|=(4233766167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884983983/2000000000 : ℝ)|^8369 ≤ (3397652772317/10000000000000 : ℝ)^6321
        have hw : |(884983983/2000000000 : ℝ)|=(884983983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(884984011/2000000000 : ℝ)|^8369 ≤ (16988264573223/50000000000000 : ℝ)^6321
        have hw : |(884984011/2000000000 : ℝ)|=(884984011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1176_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12447/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2373/4000 : ℝ) ∧ (9989/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (104/125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5699/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5699/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5699/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5699/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5699/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5699/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5699/50000 : ℝ) ^ (523/128 : ℝ) ≤ (14004281208338671/100000000000000000000 : ℝ) := by
    have hpowers : (5699/50000 : ℝ)^523 ≤ (14004281208338671/100000000000000000000 : ℝ)^128 := by
      have hnat : (5699 : ℕ)^523*100000000000000000000^128 ≤ 14004281208338671^128*50000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5699 50000 14004281208338671 100000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5699/50000 : ℝ)) (X := (14004281208338671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3517/25000 : ℝ) ^ (523/128 : ℝ) ≤ (33092582252755669/100000000000000000000 : ℝ) := by
    have hpowers : (3517/25000 : ℝ)^523 ≤ (33092582252755669/100000000000000000000 : ℝ)^128 := by
      have hnat : (3517 : ℕ)^523*100000000000000000000^128 ≤ 33092582252755669^128*25000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3517 25000 33092582252755669 100000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3517/25000 : ℝ)) (X := (33092582252755669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014004281208338671/50000000000000000000 : ℝ) ≤ (1250085676789229/1250000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (50014004281208338671/50000000000000000000 : ℝ)^128 ≤ (1250085676789229/1250000000000000 : ℝ)^523 := by
      have hnat : (50014004281208338671 : ℕ)^128*1250000000000000^523 ≤ 1250085676789229^523*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014004281208338671 50000000000000000000 1250085676789229 1250000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250085676789229/1250000000000000 : ℝ)) (X := (50014004281208338671/50000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002354843173054717/5000000000000000000 : ℝ) ≤ (5000576226258029/5000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (5002354843173054717/5000000000000000000 : ℝ)^128 ≤ (5000576226258029/5000000000000000 : ℝ)^523 := by
      have hnat : (5002354843173054717 : ℕ)^128*5000000000000000^523 ≤ 5000576226258029^523*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002354843173054717 5000000000000000000 5000576226258029 5000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000576226258029/5000000000000000 : ℝ)) (X := (5002354843173054717/5000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033092582252755669/50000000000000000000 : ℝ) ≤ (2500404872679571/2500000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (50033092582252755669/50000000000000000000 : ℝ)^128 ≤ (2500404872679571/2500000000000000 : ℝ)^523 := by
      have hnat : (50033092582252755669 : ℕ)^128*2500000000000000^523 ≤ 2500404872679571^523*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033092582252755669 50000000000000000000 2500404872679571 2500000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500404872679571/2500000000000000 : ℝ)) (X := (50033092582252755669/50000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14004281208338671/100000000000000000000 : ℝ) ≤ ((1112132643889999481/1112500000000000000 : ℝ)+2*(77839700371/44500000000000 : ℝ)*(5699/50000 : ℝ))^(523/128 : ℝ) := by
    rw [show (1112132643889999481/1112500000000000000 : ℝ)+2*(77839700371/44500000000000 : ℝ)*(5699/50000 : ℝ)=(1250085676789229/1250000000000000 : ℝ) by norm_num, show 1+2*(14004281208338671/100000000000000000000 : ℝ)=(50014004281208338671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33092582252755669/100000000000000000000 : ℝ)+(14004281208338671/100000000000000000000 : ℝ) ≤ ((1112132643889999481/1112500000000000000 : ℝ)+(77839700371/44500000000000 : ℝ)*((3517/25000 : ℝ)+(5699/50000 : ℝ)))^(523/128 : ℝ) := by
    rw [show (1112132643889999481/1112500000000000000 : ℝ)+(77839700371/44500000000000 : ℝ)*((3517/25000 : ℝ)+(5699/50000 : ℝ))=(5000576226258029/5000000000000000 : ℝ) by norm_num, show 1+(33092582252755669/100000000000000000000 : ℝ)+(14004281208338671/100000000000000000000 : ℝ)=(5002354843173054717/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33092582252755669/100000000000000000000 : ℝ) ≤ ((1112132643889999481/1112500000000000000 : ℝ)+2*(77839700371/44500000000000 : ℝ)*(3517/25000 : ℝ))^(523/128 : ℝ) := by
    rw [show (1112132643889999481/1112500000000000000 : ℝ)+2*(77839700371/44500000000000 : ℝ)*(3517/25000 : ℝ)=(2500404872679571/2500000000000000 : ℝ) by norm_num, show 1+2*(33092582252755669/100000000000000000000 : ℝ)=(50033092582252755669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1112132643889999481/1112500000000000000 : ℝ)*(X 1 0+X 2 0)+(77839700371/44500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (1112132643889999481/1112500000000000000 : ℝ)) (alpha := (77839700371/44500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1112132643889999481/1112500000000000000 : ℝ)*(X 0 1+X 2 1)+(77839700371/44500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (1112132643889999481/1112500000000000000 : ℝ)) (alpha := (77839700371/44500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1112132643889999481/1112500000000000000 : ℝ)*(X 0 2+X 1 2)+(77839700371/44500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (1112132643889999481/1112500000000000000 : ℝ)) (alpha := (77839700371/44500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2024950927/10000000000 : ℝ)*X 0 0+(2687910091/5000000000 : ℝ)*X 0 1+(2687910143/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296287979/10000000000 : ℝ)*X 1 0+(-2132893227/10000000000 : ℝ)*X 1 1+(5375820407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((662035957/1250000000 : ℝ)*X 2 0+(2687910299/5000000000 : ℝ)*X 2 1+(-533223351/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2233547111/5000000000 : ℝ)*X 0 0+(4308398919/10000000000 : ℝ)*X 0 1+(1077099731/2500000000 : ℝ)*X 0 2+(2233547111/5000000000 : ℝ)*X 1 0+(4308398919/10000000000 : ℝ)*X 1 1+(1077099731/2500000000 : ℝ)*X 1 2+(2233547111/5000000000 : ℝ)*X 2 0+(4308398919/10000000000 : ℝ)*X 2 1+(1077099731/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-569474863/2500000000 : ℝ)*X 0 0+(5281560269/10000000000 : ℝ)*X 0 1+(5281560353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681415921/5000000000 : ℝ)*X 1 0+(-2170072047/10000000000 : ℝ)*X 1 1+(5281560289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((536283181/1000000000 : ℝ)*X 2 0+(1056312063/2000000000 : ℝ)*X 2 1+(-434014411/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2126172671/5000000000 : ℝ)*X 0 0+(4415752791/10000000000 : ℝ)*X 0 1+(551969097/1250000000 : ℝ)*X 0 2+(2126172671/5000000000 : ℝ)*X 1 0+(4415752791/10000000000 : ℝ)*X 1 1+(551969097/1250000000 : ℝ)*X 1 2+(2126172671/5000000000 : ℝ)*X 2 0+(4415752791/10000000000 : ℝ)*X 2 1+(551969097/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2224965629/10000000000 : ℝ)*X 0 0+(5217389347/10000000000 : ℝ)*X 0 1+(269271569/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289499977/10000000000 : ℝ)*X 1 0+(-2129034041/10000000000 : ℝ)*X 1 1+(215417241/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289499871/10000000000 : ℝ)*X 2 0+(5385430811/10000000000 : ℝ)*X 2 1+(-2129034473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4488717349/10000000000 : ℝ)*X 0 0+(2148723401/5000000000 : ℝ)*X 0 1+(859489369/2000000000 : ℝ)*X 0 2+(4488717349/10000000000 : ℝ)*X 1 0+(2148723401/5000000000 : ℝ)*X 1 1+(859489369/2000000000 : ℝ)*X 1 2+(4488717349/10000000000 : ℝ)*X 2 0+(2148723401/5000000000 : ℝ)*X 2 1+(859489369/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2078183247/10000000000 : ℝ)*X 0 0+(5438737557/10000000000 : ℝ)*X 0 1+(5273506601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368515251/10000000000 : ℝ)*X 1 0+(-27164901/125000000 : ℝ)*X 1 1+(5273506327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368515299/10000000000 : ℝ)*X 2 0+(2636753433/5000000000 : ℝ)*X 2 1+(-1086595649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4233766167/10000000000 : ℝ)*X 0 0+(884983983/2000000000 : ℝ)*X 0 1+(884984011/2000000000 : ℝ)*X 0 2+(4233766167/10000000000 : ℝ)*X 1 0+(884983983/2000000000 : ℝ)*X 1 1+(884984011/2000000000 : ℝ)*X 1 2+(4233766167/10000000000 : ℝ)*X 2 0+(884983983/2000000000 : ℝ)*X 2 1+(884984011/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12447/20000 : ℝ) ≤ (-4327137386486054147581366584213/6953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13165169/100000000000000 : ℝ)*(lower0) + (1846613/50000000000000 : ℝ)*(lower3) + (14602633/100000000000000 : ℝ)*(lower4) + (493601782117883/12500000000000 : ℝ)*(major0) + (493601782117883/12500000000000 : ℝ)*(major1) + (493601782117883/12500000000000 : ℝ)*(major2) + (3002121111/100000000000000 : ℝ)*(sp1) + (106140263/4000000000000 : ℝ)*(sp2) + (270770137/100000000000000 : ℝ)*(sp3) + (2644119512838279/50000000000000 : ℝ)*(sp4) + (264411916247737/5000000000000 : ℝ)*(sp5) + (1322059668392319/25000000000000 : ℝ)*(sp6) + (65753281127099/2500000000000 : ℝ)*(sp7) + (2301399293/100000000000000 : ℝ)*(sp12) + (1315065757927049/50000000000000 : ℝ)*(f.failure) + (5288241327075851/100000000000000 : ℝ)*(f.sum) + (948506149669/2225000000000000000000000000 : ℝ)*base65 + (3115729975956223/13906250000000000000000000000000 : ℝ)*base67 + (175373727419549973/13906250000000000000000000000000 : ℝ)*base69 + (29897469963575027/13906250000000000000000000000000 : ℝ)*base72 + (14460854345197/1112500000000000000000000000 : ℝ)*base73 + (114198826899237473/13906250000000000000000000000000 : ℝ)*base75 + (63461416133456223/13906250000000000000000000000000 : ℝ)*base77 + (110632006328612473/13906250000000000000000000000000 : ℝ)*base79 + (3595307956361/556250000000000000000000000 : ℝ)*base81 + (35705529/5000000000000000000000 : ℝ)*base89 + (35705529/5000000000000000000000 : ℝ)*base91 + (35705529/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (2373/4000 : ℝ) ≤ (330008640427401909790013691/556250000000000000000000000 : ℝ) := by norm_num
    linear_combination (88399251/100000000000000 : ℝ)*(lower0) + (6384817/5000000000000 : ℝ)*(upper2) + (52963579/100000000000000 : ℝ)*(lower4) + (2006765721646711/50000000000000 : ℝ)*(major0) + (2006765721646711/50000000000000 : ℝ)*(major1) + (2006765721646711/50000000000000 : ℝ)*(major2) + (5334045409517331/100000000000000 : ℝ)*(sp0) + (2667019072210801/50000000000000 : ℝ)*(sp1) + (1066807880460207/20000000000000 : ℝ)*(sp2) + (1336615905998691/50000000000000 : ℝ)*(sp3) + (12155934057/100000000000000 : ℝ)*(sp5) + (340564207/3125000000000 : ℝ)*(sp6) + (1243889123/25000000000000 : ℝ)*(sp7) + (4890838329/100000000000000 : ℝ)*(sp12) + (1336618393776937/50000000000000 : ℝ)*(f.failure) + (5334050300355659/100000000000000 : ℝ)*(f.sum) + (24142737252881/1112500000000000000000000000 : ℝ)*base65 + (468452264796756991/55625000000000000000000000000000 : ℝ)*base67 + (239683434746993009/55625000000000000000000000000000 : ℝ)*base70 + (2644142326362618009/55625000000000000000000000000000 : ℝ)*base72 + (7620466863737/2225000000000000000000000000 : ℝ)*base73 + (64395740135506991/55625000000000000000000000000000 : ℝ)*base75 + (288921311532618009/55625000000000000000000000000000 : ℝ)*base78 + (1171865489449881991/55625000000000000000000000000000 : ℝ)*base79 + (2927209416469/1112500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (48153177/5000000000000000000000 : ℝ)*base89 + (48153177/5000000000000000000000 : ℝ)*base91 + (48153177/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (9989/12500 : ℝ) ≤ (5556530067138191196539461919397/6953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57662623/20000000000000 : ℝ)*(upper0) + (132106407/100000000000000 : ℝ)*(upper1) + (45903423/50000000000000 : ℝ)*(upper2) + (384118147/100000000000000 : ℝ)*(lower5) + (280067732680001/6250000000000 : ℝ)*(major0) + (280067732680001/6250000000000 : ℝ)*(major1) + (280067732680001/6250000000000 : ℝ)*(major2) + (661266779/1562500000000 : ℝ)*(sp1) + (3438525217/20000000000000 : ℝ)*(sp3) + (11535736427/100000000000000 : ℝ)*(sp4) + (1487716266064231/25000000000000 : ℝ)*(sp8) + (1190166855783899/20000000000000 : ℝ)*(sp9) + (5950876599993351/100000000000000 : ℝ)*(sp10) + (1492317803188391/50000000000000 : ℝ)*(sp11) + (1492326399501433/50000000000000 : ℝ)*(f.failure) + (5950876599993351/100000000000000 : ℝ)*(f.sum) + (1508256605591/556250000000000000000000000 : ℝ)*base66 + (27915968340551769/6953125000000000000000000000000 : ℝ)*base68 + (1782068229189759/434570312500000000000000000000 : ℝ)*base70 + (4059305634064947/3476562500000000000000000000000 : ℝ)*base72 + (41598136603/4345703125000000000000000 : ℝ)*base73 + (5567511174569089/1738281250000000000000000000000 : ℝ)*base75 + (6598211059863893/869140625000000000000000000000 : ℝ)*base78 + (46152139053833019/6953125000000000000000000000000 : ℝ)*base80 + (4445550597139/2225000000000000000000000000 : ℝ)*base82 + (13432407/5000000000000000000000 : ℝ)*base90 + (13432407/5000000000000000000000 : ℝ)*base92 + (13432407/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-104/125 : ℝ) ≤ (-23139395561516604511297435187727/27812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16643057/50000000000000 : ℝ)*(lower1) + (155255129/50000000000000 : ℝ)*(lower2) + (327582533/100000000000000 : ℝ)*(upper5) + (2258117674366937/50000000000000 : ℝ)*(major0) + (2258117674366937/50000000000000 : ℝ)*(major1) + (2258117674366937/50000000000000 : ℝ)*(major2) + (6269374897/25000000000000 : ℝ)*(sp0) + (565798327283/100000000000000 : ℝ)*(sp5) + (70566394193/100000000000000 : ℝ)*(sp6) + (23985692861/20000000000000 : ℝ)*(sp7) + (756514059724077/12500000000000 : ℝ)*(sp12) + (6051571756964921/100000000000000 : ℝ)*(sp13) + (6052066988898011/100000000000000 : ℝ)*(sp14) + (300794582262391/10000000000000 : ℝ)*(sp15) + (1504032875544107/50000000000000 : ℝ)*(f.failure) + (1513034388823051/25000000000000 : ℝ)*(f.sum) + (3756626924223/1112500000000000000000000000 : ℝ)*base66 + (714787517186390303/55625000000000000000000000000000 : ℝ)*base68 + (275134141067015303/55625000000000000000000000000000 : ℝ)*base70 + (248481401346390303/55625000000000000000000000000000 : ℝ)*base72 + (17642808394323/1112500000000000000000000000 : ℝ)*base74 + (498553042148265303/55625000000000000000000000000000 : ℝ)*base76 + (412775076607640303/55625000000000000000000000000000 : ℝ)*base78 + (203812384172015303/55625000000000000000000000000000 : ℝ)*base80 + (20006279045071/2225000000000000000000000000 : ℝ)*base82 + (51138747/5000000000000000000000 : ℝ)*base89 + (51138747/5000000000000000000000 : ℝ)*base91 + (51138747/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1176_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(2373/4000 : ℝ) else (9989/12500 : ℝ) ≤ X j i ∧ X j i ≤ (104/125 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1176_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1176_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(2373/4000 : ℝ) else (9989/12500 : ℝ) ≤ X j i ∧ X j i ≤ (104/125 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1176_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1176_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(2373/4000 : ℝ) else (9989/12500 : ℝ) ≤ X j i ∧ X j i ≤ (104/125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1176_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
