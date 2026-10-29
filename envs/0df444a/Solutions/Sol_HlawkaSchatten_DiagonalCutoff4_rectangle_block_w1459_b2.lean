-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1459_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:48.806611+00:00
-- url     : https://prove2.me/submissions/b28bd11c-cfe8-4183-9ca3-5734fd0cb0cf

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
theorem support_rectangle_w1459_s6_0 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-121690399/625000000 : ℝ)*x 0 + (5406676113/10000000000 : ℝ)*x 1 + (5247534979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121690399/625000000 : ℝ)^4419 ≤ (2377212205303/20000000000000 : ℝ)^3395 := by
    have hnat : (121690399 : ℕ)^4419*20000000000000^3395 ≤ 2377212205303^3395*625000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121690399 625000000 2377212205303 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406676113/10000000000 : ℝ)^4419 ≤ (22456744804889/50000000000000 : ℝ)^3395 := by
    have hnat : (5406676113 : ℕ)^4419*50000000000000^3395 ≤ 22456744804889^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406676113 10000000000 22456744804889 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247534979/10000000000 : ℝ)^4419 ≤ (43200449358491/100000000000000 : ℝ)^3395 := by
    have hnat : (5247534979 : ℕ)^4419*100000000000000^3395 ≤ 43200449358491^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247534979 10000000000 43200449358491 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121690399/625000000 : ℝ), (5406676113/10000000000 : ℝ), (5247534979/10000000000 : ℝ)] ![(2377212205303/20000000000000 : ℝ), (22456744804889/50000000000000 : ℝ), (43200449358491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121690399/625000000 : ℝ)|^4419 ≤ (2377212205303/20000000000000 : ℝ)^3395
        have hw : |(-121690399/625000000 : ℝ)|=(121690399/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406676113/10000000000 : ℝ)|^4419 ≤ (22456744804889/50000000000000 : ℝ)^3395
        have hw : |(5406676113/10000000000 : ℝ)|=(5406676113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247534979/10000000000 : ℝ)|^4419 ≤ (43200449358491/100000000000000 : ℝ)^3395
        have hw : |(5247534979/10000000000 : ℝ)|=(5247534979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s6_1 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346679609/10000000000 : ℝ)*x 0 + (-63376489/312500000 : ℝ)*x 1 + (5247534861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346679609/10000000000 : ℝ)^4419 ≤ (44265859066009/100000000000000 : ℝ)^3395 := by
    have hnat : (5346679609 : ℕ)^4419*100000000000000^3395 ≤ 44265859066009^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346679609 10000000000 44265859066009 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63376489/312500000 : ℝ)^4419 ≤ (12239934399/97656250000 : ℝ)^3395 := by
    have hnat : (63376489 : ℕ)^4419*97656250000^3395 ≤ 12239934399^3395*312500000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63376489 312500000 12239934399 97656250000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247534861/10000000000 : ℝ)^4419 ≤ (43200448094049/100000000000000 : ℝ)^3395 := by
    have hnat : (5247534861 : ℕ)^4419*100000000000000^3395 ≤ 43200448094049^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247534861 10000000000 43200448094049 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346679609/10000000000 : ℝ), (-63376489/312500000 : ℝ), (5247534861/10000000000 : ℝ)] ![(44265859066009/100000000000000 : ℝ), (12239934399/97656250000 : ℝ), (43200448094049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346679609/10000000000 : ℝ)|^4419 ≤ (44265859066009/100000000000000 : ℝ)^3395
        have hw : |(5346679609/10000000000 : ℝ)|=(5346679609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-63376489/312500000 : ℝ)|^4419 ≤ (12239934399/97656250000 : ℝ)^3395
        have hw : |(-63376489/312500000 : ℝ)|=(63376489/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247534861/10000000000 : ℝ)|^4419 ≤ (43200448094049/100000000000000 : ℝ)^3395
        have hw : |(5247534861/10000000000 : ℝ)|=(5247534861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s6_2 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346679453/10000000000 : ℝ)*x 0 + (1049507023/2000000000 : ℝ)*x 1 + (-1014023759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346679453/10000000000 : ℝ)^4419 ≤ (44265857384909/100000000000000 : ℝ)^3395 := by
    have hnat : (5346679453 : ℕ)^4419*100000000000000^3395 ≤ 44265857384909^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346679453 10000000000 44265857384909 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049507023/2000000000 : ℝ)^4419 ≤ (8640090163163/20000000000000 : ℝ)^3395 := by
    have hnat : (1049507023 : ℕ)^4419*20000000000000^3395 ≤ 8640090163163^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049507023 2000000000 8640090163163 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1014023759/5000000000 : ℝ)^4419 ≤ (1566711472353/12500000000000 : ℝ)^3395 := by
    have hnat : (1014023759 : ℕ)^4419*12500000000000^3395 ≤ 1566711472353^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014023759 5000000000 1566711472353 12500000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346679453/10000000000 : ℝ), (1049507023/2000000000 : ℝ), (-1014023759/5000000000 : ℝ)] ![(44265857384909/100000000000000 : ℝ), (8640090163163/20000000000000 : ℝ), (1566711472353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346679453/10000000000 : ℝ)|^4419 ≤ (44265857384909/100000000000000 : ℝ)^3395
        have hw : |(5346679453/10000000000 : ℝ)|=(5346679453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049507023/2000000000 : ℝ)|^4419 ≤ (8640090163163/20000000000000 : ℝ)^3395
        have hw : |(1049507023/2000000000 : ℝ)|=(1049507023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1014023759/5000000000 : ℝ)|^4419 ≤ (1566711472353/12500000000000 : ℝ)^3395
        have hw : |(-1014023759/5000000000 : ℝ)|=(1014023759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s6_3 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4296928417/10000000000 : ℝ)*x 0 + (2063012831/5000000000 : ℝ)*x 1 + (2237044463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296928417/10000000000 : ℝ)^4419 ≤ (3330513970781/10000000000000 : ℝ)^3395 := by
    have hnat : (4296928417 : ℕ)^4419*10000000000000^3395 ≤ 3330513970781^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296928417 10000000000 3330513970781 10000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063012831/5000000000 : ℝ)^4419 ≤ (31591384005263/100000000000000 : ℝ)^3395 := by
    have hnat : (2063012831 : ℕ)^4419*100000000000000^3395 ≤ 31591384005263^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063012831 5000000000 31591384005263 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237044463/5000000000 : ℝ)^4419 ≤ (3510347627527/10000000000000 : ℝ)^3395 := by
    have hnat : (2237044463 : ℕ)^4419*10000000000000^3395 ≤ 3510347627527^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237044463 5000000000 3510347627527 10000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296928417/10000000000 : ℝ), (2063012831/5000000000 : ℝ), (2237044463/5000000000 : ℝ)] ![(3330513970781/10000000000000 : ℝ), (31591384005263/100000000000000 : ℝ), (3510347627527/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296928417/10000000000 : ℝ)|^4419 ≤ (3330513970781/10000000000000 : ℝ)^3395
        have hw : |(4296928417/10000000000 : ℝ)|=(4296928417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063012831/5000000000 : ℝ)|^4419 ≤ (31591384005263/100000000000000 : ℝ)^3395
        have hw : |(2063012831/5000000000 : ℝ)|=(2063012831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237044463/5000000000 : ℝ)|^4419 ≤ (3510347627527/10000000000000 : ℝ)^3395
        have hw : |(2237044463/5000000000 : ℝ)|=(2237044463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s6_4 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1947057329/10000000000 : ℝ)*x 0 + (5248110573/10000000000 : ℝ)*x 1 + (5406097619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1947057329/10000000000 : ℝ)^4419 ≤ (5943073997511/50000000000000 : ℝ)^3395 := by
    have hnat : (1947057329 : ℕ)^4419*50000000000000^3395 ≤ 5943073997511^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947057329 10000000000 5943073997511 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5248110573/10000000000 : ℝ)^4419 ≤ (10801654326209/25000000000000 : ℝ)^3395 := by
    have hnat : (5248110573 : ℕ)^4419*25000000000000^3395 ≤ 10801654326209^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248110573 10000000000 10801654326209 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406097619/10000000000 : ℝ)^4419 ≤ (8981446935767/20000000000000 : ℝ)^3395 := by
    have hnat : (5406097619 : ℕ)^4419*20000000000000^3395 ≤ 8981446935767^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406097619 10000000000 8981446935767 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1947057329/10000000000 : ℝ), (5248110573/10000000000 : ℝ), (5406097619/10000000000 : ℝ)] ![(5943073997511/50000000000000 : ℝ), (10801654326209/25000000000000 : ℝ), (8981446935767/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1947057329/10000000000 : ℝ)|^4419 ≤ (5943073997511/50000000000000 : ℝ)^3395
        have hw : |(-1947057329/10000000000 : ℝ)|=(1947057329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5248110573/10000000000 : ℝ)|^4419 ≤ (10801654326209/25000000000000 : ℝ)^3395
        have hw : |(5248110573/10000000000 : ℝ)|=(5248110573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406097619/10000000000 : ℝ)|^4419 ≤ (8981446935767/20000000000000 : ℝ)^3395
        have hw : |(5406097619/10000000000 : ℝ)|=(5406097619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s6_5 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41446787/78125000 : ℝ)*x 0 + (-1869485001/10000000000 : ℝ)*x 1 + (5406097611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41446787/78125000 : ℝ)^4419 ≤ (43819265917623/100000000000000 : ℝ)^3395 := by
    have hnat : (41446787 : ℕ)^4419*100000000000000^3395 ≤ 43819265917623^3395*78125000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41446787 78125000 43819265917623 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1869485001/10000000000 : ℝ)^4419 ≤ (704593717009/6250000000000 : ℝ)^3395 := by
    have hnat : (1869485001 : ℕ)^4419*6250000000000^3395 ≤ 704593717009^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869485001 10000000000 704593717009 6250000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406097611/10000000000 : ℝ)^4419 ≤ (44907234592337/100000000000000 : ℝ)^3395 := by
    have hnat : (5406097611 : ℕ)^4419*100000000000000^3395 ≤ 44907234592337^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406097611 10000000000 44907234592337 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41446787/78125000 : ℝ), (-1869485001/10000000000 : ℝ), (5406097611/10000000000 : ℝ)] ![(43819265917623/100000000000000 : ℝ), (704593717009/6250000000000 : ℝ), (44907234592337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41446787/78125000 : ℝ)|^4419 ≤ (43819265917623/100000000000000 : ℝ)^3395
        have hw : |(41446787/78125000 : ℝ)|=(41446787/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1869485001/10000000000 : ℝ)|^4419 ≤ (704593717009/6250000000000 : ℝ)^3395
        have hw : |(-1869485001/10000000000 : ℝ)|=(1869485001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406097611/10000000000 : ℝ)|^4419 ≤ (44907234592337/100000000000000 : ℝ)^3395
        have hw : |(5406097611/10000000000 : ℝ)|=(5406097611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s6_6 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305188723/10000000000 : ℝ)*x 0 + (540609761/1000000000 : ℝ)*x 1 + (-93474251/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305188723/10000000000 : ℝ)^4419 ≤ (2190963288893/5000000000000 : ℝ)^3395 := by
    have hnat : (5305188723 : ℕ)^4419*5000000000000^3395 ≤ 2190963288893^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305188723 10000000000 2190963288893 5000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540609761/1000000000 : ℝ)^4419 ≤ (1796289383261/4000000000000 : ℝ)^3395 := by
    have hnat : (540609761 : ℕ)^4419*4000000000000^3395 ≤ 1796289383261^3395*1000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540609761 1000000000 1796289383261 4000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93474251/500000000 : ℝ)^4419 ≤ (11273499621277/100000000000000 : ℝ)^3395 := by
    have hnat : (93474251 : ℕ)^4419*100000000000000^3395 ≤ 11273499621277^3395*500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93474251 500000000 11273499621277 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305188723/10000000000 : ℝ), (540609761/1000000000 : ℝ), (-93474251/500000000 : ℝ)] ![(2190963288893/5000000000000 : ℝ), (1796289383261/4000000000000 : ℝ), (11273499621277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305188723/10000000000 : ℝ)|^4419 ≤ (2190963288893/5000000000000 : ℝ)^3395
        have hw : |(5305188723/10000000000 : ℝ)|=(5305188723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540609761/1000000000 : ℝ)|^4419 ≤ (1796289383261/4000000000000 : ℝ)^3395
        have hw : |(540609761/1000000000 : ℝ)|=(540609761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-93474251/500000000 : ℝ)|^4419 ≤ (11273499621277/100000000000000 : ℝ)^3395
        have hw : |(-93474251/500000000 : ℝ)|=(93474251/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s6_7 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (859390467/2000000000 : ℝ)*x 0 + (4472830219/10000000000 : ℝ)*x 1 + (128977849/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859390467/2000000000 : ℝ)^4419 ≤ (33305381010737/100000000000000 : ℝ)^3395 := by
    have hnat : (859390467 : ℕ)^4419*100000000000000^3395 ≤ 33305381010737^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859390467 2000000000 33305381010737 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4472830219/10000000000 : ℝ)^4419 ≤ (8772655586119/25000000000000 : ℝ)^3395 := by
    have hnat : (4472830219 : ℕ)^4419*25000000000000^3395 ≤ 8772655586119^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472830219 10000000000 8772655586119 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128977849/312500000 : ℝ)^4419 ≤ (6320799324673/20000000000000 : ℝ)^3395 := by
    have hnat : (128977849 : ℕ)^4419*20000000000000^3395 ≤ 6320799324673^3395*312500000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128977849 312500000 6320799324673 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859390467/2000000000 : ℝ), (4472830219/10000000000 : ℝ), (128977849/312500000 : ℝ)] ![(33305381010737/100000000000000 : ℝ), (8772655586119/25000000000000 : ℝ), (6320799324673/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859390467/2000000000 : ℝ)|^4419 ≤ (33305381010737/100000000000000 : ℝ)^3395
        have hw : |(859390467/2000000000 : ℝ)|=(859390467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4472830219/10000000000 : ℝ)|^4419 ≤ (8772655586119/25000000000000 : ℝ)^3395
        have hw : |(4472830219/10000000000 : ℝ)|=(4472830219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128977849/312500000 : ℝ)|^4419 ≤ (6320799324673/20000000000000 : ℝ)^3395
        have hw : |(128977849/312500000 : ℝ)|=(128977849/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1459_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (591/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (57/500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3693/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (591/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (591/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (591/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (591/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (591/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (591/4000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11397/100000 : ℝ) ^ (2209/512 : ℝ) ≤ (4261250231285359/50000000000000000000 : ℝ) := by
    have hpowers : (11397/100000 : ℝ)^2209 ≤ (4261250231285359/50000000000000000000 : ℝ)^512 := by
      have hnat : (11397 : ℕ)^2209*50000000000000000000^512 ≤ 4261250231285359^512*100000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11397 100000 4261250231285359 50000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11397/100000 : ℝ)) (X := (4261250231285359/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hpowhi : (591/4000 : ℝ) ^ (2209/512 : ℝ) ≤ (26119525440256367/100000000000000000000 : ℝ) := by
    have hpowers : (591/4000 : ℝ)^2209 ≤ (26119525440256367/100000000000000000000 : ℝ)^512 := by
      have hnat : (591 : ℕ)^2209*100000000000000000000^512 ≤ 26119525440256367^512*4000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        591 4000 26119525440256367 100000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (591/4000 : ℝ)) (X := (26119525440256367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004261250231285359/25000000000000000000 : ℝ) ≤ (2000079008321933/2000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (25004261250231285359/25000000000000000000 : ℝ)^512 ≤ (2000079008321933/2000000000000000 : ℝ)^2209 := by
      have hnat : (25004261250231285359 : ℕ)^512*2000000000000000^2209 ≤ 2000079008321933^2209*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004261250231285359 25000000000000000000 2000079008321933 2000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000079008321933/2000000000000000 : ℝ)) (X := (25004261250231285359/25000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006928405180565417/20000000000000000000 : ℝ) ≤ (1250100352861203/1250000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (20006928405180565417/20000000000000000000 : ℝ)^512 ≤ (1250100352861203/1250000000000000 : ℝ)^2209 := by
      have hnat : (20006928405180565417 : ℕ)^512*1250000000000000^2209 ≤ 1250100352861203^2209*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006928405180565417 20000000000000000000 1250100352861203 1250000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250100352861203/1250000000000000 : ℝ)) (X := (20006928405180565417/20000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026119525440256367/50000000000000000000 : ℝ) ≤ (10001210604169583/10000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (50026119525440256367/50000000000000000000 : ℝ)^512 ≤ (10001210604169583/10000000000000000 : ℝ)^2209 := by
      have hnat : (50026119525440256367 : ℕ)^512*10000000000000000^2209 ≤ 10001210604169583^2209*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026119525440256367 50000000000000000000 10001210604169583 10000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001210604169583/10000000000000000 : ℝ)) (X := (50026119525440256367/50000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4261250231285359/50000000000000000000 : ℝ) ≤ ((2814336623671838577/2815000000000000000 : ℝ)+2*(407781279959/337800000000000 : ℝ)*(11397/100000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (2814336623671838577/2815000000000000000 : ℝ)+2*(407781279959/337800000000000 : ℝ)*(11397/100000 : ℝ)=(2000079008321933/2000000000000000 : ℝ) by norm_num, show 1+2*(4261250231285359/50000000000000000000 : ℝ)=(25004261250231285359/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26119525440256367/100000000000000000000 : ℝ)+(4261250231285359/50000000000000000000 : ℝ) ≤ ((2814336623671838577/2815000000000000000 : ℝ)+(407781279959/337800000000000 : ℝ)*((591/4000 : ℝ)+(11397/100000 : ℝ)))^(2209/512 : ℝ) := by
    rw [show (2814336623671838577/2815000000000000000 : ℝ)+(407781279959/337800000000000 : ℝ)*((591/4000 : ℝ)+(11397/100000 : ℝ))=(1250100352861203/1250000000000000 : ℝ) by norm_num, show 1+(26119525440256367/100000000000000000000 : ℝ)+(4261250231285359/50000000000000000000 : ℝ)=(20006928405180565417/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26119525440256367/100000000000000000000 : ℝ) ≤ ((2814336623671838577/2815000000000000000 : ℝ)+2*(407781279959/337800000000000 : ℝ)*(591/4000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (2814336623671838577/2815000000000000000 : ℝ)+2*(407781279959/337800000000000 : ℝ)*(591/4000 : ℝ)=(10001210604169583/10000000000000000 : ℝ) by norm_num, show 1+2*(26119525440256367/100000000000000000000 : ℝ)=(50026119525440256367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2814336623671838577/2815000000000000000 : ℝ)*(X 1 0+X 2 0)+(407781279959/337800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (591/4000 : ℝ)) (c := (2814336623671838577/2815000000000000000 : ℝ)) (alpha := (407781279959/337800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2814336623671838577/2815000000000000000 : ℝ)*(X 0 1+X 2 1)+(407781279959/337800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (591/4000 : ℝ)) (c := (2814336623671838577/2815000000000000000 : ℝ)) (alpha := (407781279959/337800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2814336623671838577/2815000000000000000 : ℝ)*(X 0 2+X 1 2)+(407781279959/337800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (591/4000 : ℝ)) (c := (2814336623671838577/2815000000000000000 : ℝ)) (alpha := (407781279959/337800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-121690399/625000000 : ℝ)*X 0 0+(5406676113/10000000000 : ℝ)*X 0 1+(5247534979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346679609/10000000000 : ℝ)*X 1 0+(-63376489/312500000 : ℝ)*X 1 1+(5247534861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346679453/10000000000 : ℝ)*X 2 0+(1049507023/2000000000 : ℝ)*X 2 1+(-1014023759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4296928417/10000000000 : ℝ)*X 0 0+(2063012831/5000000000 : ℝ)*X 0 1+(2237044463/5000000000 : ℝ)*X 0 2+(4296928417/10000000000 : ℝ)*X 1 0+(2063012831/5000000000 : ℝ)*X 1 1+(2237044463/5000000000 : ℝ)*X 1 2+(4296928417/10000000000 : ℝ)*X 2 0+(2063012831/5000000000 : ℝ)*X 2 1+(2237044463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1947057329/10000000000 : ℝ)*X 0 0+(5248110573/10000000000 : ℝ)*X 0 1+(5406097619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41446787/78125000 : ℝ)*X 1 0+(-1869485001/10000000000 : ℝ)*X 1 1+(5406097611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305188723/10000000000 : ℝ)*X 2 0+(540609761/1000000000 : ℝ)*X 2 1+(-93474251/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859390467/2000000000 : ℝ)*X 0 0+(4472830219/10000000000 : ℝ)*X 0 1+(128977849/312500000 : ℝ)*X 0 2+(859390467/2000000000 : ℝ)*X 1 0+(4472830219/10000000000 : ℝ)*X 1 1+(128977849/312500000 : ℝ)*X 1 2+(859390467/2000000000 : ℝ)*X 2 0+(4472830219/10000000000 : ℝ)*X 2 1+(128977849/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (195140020650873828211479393/35187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1540985097/100000000000000 : ℝ)*(base19) + (1269911893/100000000000000 : ℝ)*(base23) + (1876281/4000000000000 : ℝ)*(lower2) + (37402523/25000000000000 : ℝ)*(upper3) + (223346691/100000000000000 : ℝ)*(upper5) + (1144607652385401/25000000000000 : ℝ)*(major0) + (1144607652385401/25000000000000 : ℝ)*(major1) + (1144607652385401/25000000000000 : ℝ)*(major2) + (3141879829379281/50000000000000 : ℝ)*(sp0) + (1256758038545763/20000000000000 : ℝ)*(sp1) + (3141895231901009/50000000000000 : ℝ)*(sp2) + (71826393405951/2500000000000 : ℝ)*(sp3) + (641499107/2000000000000 : ℝ)*(sp4) + (3391068479/25000000000000 : ℝ)*(sp7) + (718267325127989/25000000000000 : ℝ)*(f.failure) + (785473966714239/12500000000000 : ℝ)*(f.sum) + (752009119211/175937500000000000000000000 : ℝ)*base65 + (715978291692760623/70375000000000000000000000000000 : ℝ)*base68 + (939009027076260623/70375000000000000000000000000000 : ℝ)*base70 + (51393016168385623/70375000000000000000000000000000 : ℝ)*base72 + (886444296023/1407500000000000000000000000 : ℝ)*base73 + (1674756278216385623/70375000000000000000000000000000 : ℝ)*base76 + (380276702055510623/70375000000000000000000000000000 : ℝ)*base78 + (478484976553010623/70375000000000000000000000000000 : ℝ)*base80 + (4603715640223/1407500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1800433/312500000000000000000 : ℝ)*base89 + (1800433/312500000000000000000 : ℝ)*base91 + (1800433/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145465763420998486301890407/17593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (277780263/20000000000000 : ℝ)*(base19) + (298861743/20000000000000 : ℝ)*(base23) + (472196077/100000000000000 : ℝ)*(lower1) + (8039397/5000000000000 : ℝ)*(upper3) + (29406213/50000000000000 : ℝ)*(lower4) + (5317131/3125000000000 : ℝ)*(upper5) + (576476044760847/12500000000000 : ℝ)*(major0) + (576476044760847/12500000000000 : ℝ)*(major1) + (576476044760847/12500000000000 : ℝ)*(major2) + (643114977/50000000000000 : ℝ)*(sp2) + (3164800921993813/50000000000000 : ℝ)*(sp4) + (632960045508631/10000000000000 : ℝ)*(sp5) + (6329599063448957/100000000000000 : ℝ)*(sp6) + (578802919316939/20000000000000 : ℝ)*(sp7) + (578802919316939/20000000000000 : ℝ)*(f.failure) + (3164800921993813/50000000000000 : ℝ)*(f.sum) + (5890699853499/2815000000000000000000000000 : ℝ)*base65 + (990634738705742781/35187500000000000000000000000000 : ℝ)*base68 + (271784793693444719/35187500000000000000000000000000 : ℝ)*base69 + (2741267372028617781/35187500000000000000000000000000 : ℝ)*base72 + (3451333385939/2815000000000000000000000000 : ℝ)*base73 + (2504711035163305281/35187500000000000000000000000000 : ℝ)*base76 + (254483807029805281/35187500000000000000000000000000 : ℝ)*base78 + (139490721840132219/35187500000000000000000000000000 : ℝ)*base79 + (3029726358561/703750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (153583/250000000000000000000 : ℝ)*base89 + (153583/250000000000000000000 : ℝ)*base91 + (153583/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1459_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (591/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1459_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1459_s7_0 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-24338101/125000000 : ℝ)*x 0 + (675831947/1250000000 : ℝ)*x 1 + (1311888611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24338101/125000000 : ℝ)^4419 ≤ (237721490057/2000000000000 : ℝ)^3395 := by
    have hnat : (24338101 : ℕ)^4419*2000000000000^3395 ≤ 237721490057^3395*125000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24338101 125000000 237721490057 2000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675831947/1250000000 : ℝ)^4419 ≤ (11228316887817/25000000000000 : ℝ)^3395 := by
    have hnat : (675831947 : ℕ)^4419*25000000000000^3395 ≤ 11228316887817^3395*1250000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675831947 1250000000 11228316887817 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311888611/2500000000 : ℝ)^4419 ≤ (1728026317523/4000000000000 : ℝ)^3395 := by
    have hnat : (1311888611 : ℕ)^4419*4000000000000^3395 ≤ 1728026317523^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311888611 2500000000 1728026317523 4000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24338101/125000000 : ℝ), (675831947/1250000000 : ℝ), (1311888611/2500000000 : ℝ)] ![(237721490057/2000000000000 : ℝ), (11228316887817/25000000000000 : ℝ), (1728026317523/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24338101/125000000 : ℝ)|^4419 ≤ (237721490057/2000000000000 : ℝ)^3395
        have hw : |(-24338101/125000000 : ℝ)|=(24338101/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675831947/1250000000 : ℝ)|^4419 ≤ (11228316887817/25000000000000 : ℝ)^3395
        have hw : |(675831947/1250000000 : ℝ)|=(675831947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311888611/2500000000 : ℝ)|^4419 ≤ (1728026317523/4000000000000 : ℝ)^3395
        have hw : |(1311888611/2500000000 : ℝ)|=(1311888611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s7_1 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346674337/10000000000 : ℝ)*x 0 + (-2028028719/10000000000 : ℝ)*x 1 + (5247554373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346674337/10000000000 : ℝ)^4419 ≤ (44265802253457/100000000000000 : ℝ)^3395 := by
    have hnat : (5346674337 : ℕ)^4419*100000000000000^3395 ≤ 44265802253457^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346674337 10000000000 44265802253457 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2028028719/10000000000 : ℝ)^4419 ≤ (6266770277669/50000000000000 : ℝ)^3395 := by
    have hnat : (2028028719 : ℕ)^4419*50000000000000^3395 ≤ 6266770277669^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028028719 10000000000 6266770277669 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247554373/10000000000 : ℝ)^4419 ≤ (8640131435453/20000000000000 : ℝ)^3395 := by
    have hnat : (5247554373 : ℕ)^4419*20000000000000^3395 ≤ 8640131435453^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247554373 10000000000 8640131435453 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346674337/10000000000 : ℝ), (-2028028719/10000000000 : ℝ), (5247554373/10000000000 : ℝ)] ![(44265802253457/100000000000000 : ℝ), (6266770277669/50000000000000 : ℝ), (8640131435453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346674337/10000000000 : ℝ)|^4419 ≤ (44265802253457/100000000000000 : ℝ)^3395
        have hw : |(5346674337/10000000000 : ℝ)|=(5346674337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2028028719/10000000000 : ℝ)|^4419 ≤ (6266770277669/50000000000000 : ℝ)^3395
        have hw : |(-2028028719/10000000000 : ℝ)|=(2028028719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247554373/10000000000 : ℝ)|^4419 ≤ (8640131435453/20000000000000 : ℝ)^3395
        have hw : |(5247554373/10000000000 : ℝ)|=(5247554373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s7_2 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1947059459/10000000000 : ℝ)*x 0 + (5248129519/10000000000 : ℝ)*x 1 + (5406077277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1947059459/10000000000 : ℝ)^4419 ≤ (11886164919929/100000000000000 : ℝ)^3395 := by
    have hnat : (1947059459 : ℕ)^4419*100000000000000^3395 ≤ 11886164919929^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947059459 10000000000 11886164919929 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5248129519/10000000000 : ℝ)^4419 ≤ (1728272813189/4000000000000 : ℝ)^3395 := by
    have hnat : (5248129519 : ℕ)^4419*4000000000000^3395 ≤ 1728272813189^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248129519 10000000000 1728272813189 4000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406077277/10000000000 : ℝ)^4419 ≤ (1122675368397/2500000000000 : ℝ)^3395 := by
    have hnat : (5406077277 : ℕ)^4419*2500000000000^3395 ≤ 1122675368397^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406077277 10000000000 1122675368397 2500000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1947059459/10000000000 : ℝ), (5248129519/10000000000 : ℝ), (5406077277/10000000000 : ℝ)] ![(11886164919929/100000000000000 : ℝ), (1728272813189/4000000000000 : ℝ), (1122675368397/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1947059459/10000000000 : ℝ)|^4419 ≤ (11886164919929/100000000000000 : ℝ)^3395
        have hw : |(-1947059459/10000000000 : ℝ)|=(1947059459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5248129519/10000000000 : ℝ)|^4419 ≤ (1728272813189/4000000000000 : ℝ)^3395
        have hw : |(5248129519/10000000000 : ℝ)|=(5248129519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406077277/10000000000 : ℝ)|^4419 ≤ (1122675368397/2500000000000 : ℝ)^3395
        have hw : |(5406077277/10000000000 : ℝ)|=(5406077277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s7_3 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305193983/10000000000 : ℝ)*x 0 + (-934752649/5000000000 : ℝ)*x 1 + (5406077659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305193983/10000000000 : ℝ)^4419 ≤ (43819322328079/100000000000000 : ℝ)^3395 := by
    have hnat : (5305193983 : ℕ)^4419*100000000000000^3395 ≤ 43819322328079^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305193983 10000000000 43819322328079 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (934752649/5000000000 : ℝ)^4419 ≤ (5636829393/50000000000 : ℝ)^3395 := by
    have hnat : (934752649 : ℕ)^4419*50000000000^3395 ≤ 5636829393^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934752649 5000000000 5636829393 50000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406077659/10000000000 : ℝ)^4419 ≤ (561337735827/1250000000000 : ℝ)^3395 := by
    have hnat : (5406077659 : ℕ)^4419*1250000000000^3395 ≤ 561337735827^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406077659 10000000000 561337735827 1250000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305193983/10000000000 : ℝ), (-934752649/5000000000 : ℝ), (5406077659/10000000000 : ℝ)] ![(43819322328079/100000000000000 : ℝ), (5636829393/50000000000 : ℝ), (561337735827/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305193983/10000000000 : ℝ)|^4419 ≤ (43819322328079/100000000000000 : ℝ)^3395
        have hw : |(5305193983/10000000000 : ℝ)|=(5305193983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-934752649/5000000000 : ℝ)|^4419 ≤ (5636829393/50000000000 : ℝ)^3395
        have hw : |(-934752649/5000000000 : ℝ)|=(934752649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406077659/10000000000 : ℝ)|^4419 ≤ (561337735827/1250000000000 : ℝ)^3395
        have hw : |(5406077659/10000000000 : ℝ)|=(5406077659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s7_4 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305193469/10000000000 : ℝ)*x 0 + (5406077701/10000000000 : ℝ)*x 1 + (-373901189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305193469/10000000000 : ℝ)^4419 ≤ (10954829200517/25000000000000 : ℝ)^3395 := by
    have hnat : (5305193469 : ℕ)^4419*25000000000000^3395 ≤ 10954829200517^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305193469 10000000000 10954829200517 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406077701/10000000000 : ℝ)^4419 ≤ (1796280772811/4000000000000 : ℝ)^3395 := by
    have hnat : (5406077701 : ℕ)^4419*4000000000000^3395 ≤ 1796280772811^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406077701 10000000000 1796280772811 4000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373901189/2000000000 : ℝ)^4419 ≤ (5636831932199/50000000000000 : ℝ)^3395 := by
    have hnat : (373901189 : ℕ)^4419*50000000000000^3395 ≤ 5636831932199^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373901189 2000000000 5636831932199 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305193469/10000000000 : ℝ), (5406077701/10000000000 : ℝ), (-373901189/2000000000 : ℝ)] ![(10954829200517/25000000000000 : ℝ), (1796280772811/4000000000000 : ℝ), (5636831932199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305193469/10000000000 : ℝ)|^4419 ≤ (10954829200517/25000000000000 : ℝ)^3395
        have hw : |(5305193469/10000000000 : ℝ)|=(5305193469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406077701/10000000000 : ℝ)|^4419 ≤ (1796280772811/4000000000000 : ℝ)^3395
        have hw : |(5406077701/10000000000 : ℝ)|=(5406077701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-373901189/2000000000 : ℝ)|^4419 ≤ (5636831932199/50000000000000 : ℝ)^3395
        have hw : |(-373901189/2000000000 : ℝ)|=(373901189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s7_5 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4296954189/10000000000 : ℝ)*x 0 + (1118196547/2500000000 : ℝ)*x 1 + (4127334403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296954189/10000000000 : ℝ)^4419 ≤ (33305399715313/100000000000000 : ℝ)^3395 := by
    have hnat : (4296954189 : ℕ)^4419*100000000000000^3395 ≤ 33305399715313^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296954189 10000000000 33305399715313 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118196547/2500000000 : ℝ)^4419 ≤ (3509017271913/10000000000000 : ℝ)^3395 := by
    have hnat : (1118196547 : ℕ)^4419*10000000000000^3395 ≤ 3509017271913^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118196547 2500000000 3509017271913 10000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4127334403/10000000000 : ℝ)^4419 ≤ (1580221377199/5000000000000 : ℝ)^3395 := by
    have hnat : (4127334403 : ℕ)^4419*5000000000000^3395 ≤ 1580221377199^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127334403 10000000000 1580221377199 5000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296954189/10000000000 : ℝ), (1118196547/2500000000 : ℝ), (4127334403/10000000000 : ℝ)] ![(33305399715313/100000000000000 : ℝ), (3509017271913/10000000000000 : ℝ), (1580221377199/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296954189/10000000000 : ℝ)|^4419 ≤ (33305399715313/100000000000000 : ℝ)^3395
        have hw : |(4296954189/10000000000 : ℝ)|=(4296954189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118196547/2500000000 : ℝ)|^4419 ≤ (3509017271913/10000000000000 : ℝ)^3395
        have hw : |(1118196547/2500000000 : ℝ)|=(1118196547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4127334403/10000000000 : ℝ)|^4419 ≤ (1580221377199/5000000000000 : ℝ)^3395
        have hw : |(4127334403/10000000000 : ℝ)|=(4127334403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1459_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    (57/500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14771/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (57/500 : ℝ) ^ (2209/512 : ℝ) ≤ (8532183529706469/100000000000000000000 : ℝ) := by
    have hpowers : (57/500 : ℝ)^2209 ≤ (8532183529706469/100000000000000000000 : ℝ)^512 := by
      have hnat : (57 : ℕ)^2209*100000000000000000000^512 ≤ 8532183529706469^512*500^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57 500 8532183529706469 100000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57/500 : ℝ)) (X := (8532183529706469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3693/25000 : ℝ) ^ (2209/512 : ℝ) ≤ (26096651622136139/100000000000000000000 : ℝ) := by
    have hpowers : (3693/25000 : ℝ)^2209 ≤ (26096651622136139/100000000000000000000 : ℝ)^512 := by
      have hnat : (3693 : ℕ)^2209*100000000000000000000^512 ≤ 26096651622136139^512*25000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3693 25000 26096651622136139 100000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3693/25000 : ℝ)) (X := (26096651622136139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008532183529706469/50000000000000000000 : ℝ) ≤ (5000197745208677/5000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (50008532183529706469/50000000000000000000 : ℝ)^512 ≤ (5000197745208677/5000000000000000 : ℝ)^2209 := by
      have hnat : (50008532183529706469 : ℕ)^512*5000000000000000^2209 ≤ 5000197745208677^2209*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008532183529706469 50000000000000000000 5000197745208677 5000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000197745208677/5000000000000000 : ℝ)) (X := (50008532183529706469/50000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252164302196990163/6250000000000000000 : ℝ) ≤ (156262539331827/156250000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (6252164302196990163/6250000000000000000 : ℝ)^512 ≤ (156262539331827/156250000000000 : ℝ)^2209 := by
      have hnat : (6252164302196990163 : ℕ)^512*156250000000000^2209 ≤ 156262539331827^2209*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252164302196990163 6250000000000000000 156262539331827 156250000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156262539331827/156250000000000 : ℝ)) (X := (6252164302196990163/6250000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026096651622136139/50000000000000000000 : ℝ) ≤ (5000604772028251/5000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (50026096651622136139/50000000000000000000 : ℝ)^512 ≤ (5000604772028251/5000000000000000 : ℝ)^2209 := by
      have hnat : (50026096651622136139 : ℕ)^512*5000000000000000^2209 ≤ 5000604772028251^2209*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026096651622136139 50000000000000000000 5000604772028251 5000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000604772028251/5000000000000000 : ℝ)) (X := (50026096651622136139/50000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8532183529706469/100000000000000000000 : ℝ) ≤ ((1404668890925042937/1405000000000000000 : ℝ)+2*(203513409787/168600000000000 : ℝ)*(57/500 : ℝ))^(2209/512 : ℝ) := by
    rw [show (1404668890925042937/1405000000000000000 : ℝ)+2*(203513409787/168600000000000 : ℝ)*(57/500 : ℝ)=(5000197745208677/5000000000000000 : ℝ) by norm_num, show 1+2*(8532183529706469/100000000000000000000 : ℝ)=(50008532183529706469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26096651622136139/100000000000000000000 : ℝ)+(8532183529706469/100000000000000000000 : ℝ) ≤ ((1404668890925042937/1405000000000000000 : ℝ)+(203513409787/168600000000000 : ℝ)*((3693/25000 : ℝ)+(57/500 : ℝ)))^(2209/512 : ℝ) := by
    rw [show (1404668890925042937/1405000000000000000 : ℝ)+(203513409787/168600000000000 : ℝ)*((3693/25000 : ℝ)+(57/500 : ℝ))=(156262539331827/156250000000000 : ℝ) by norm_num, show 1+(26096651622136139/100000000000000000000 : ℝ)+(8532183529706469/100000000000000000000 : ℝ)=(6252164302196990163/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26096651622136139/100000000000000000000 : ℝ) ≤ ((1404668890925042937/1405000000000000000 : ℝ)+2*(203513409787/168600000000000 : ℝ)*(3693/25000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (1404668890925042937/1405000000000000000 : ℝ)+2*(203513409787/168600000000000 : ℝ)*(3693/25000 : ℝ)=(5000604772028251/5000000000000000 : ℝ) by norm_num, show 1+2*(26096651622136139/100000000000000000000 : ℝ)=(50026096651622136139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1404668890925042937/1405000000000000000 : ℝ)*(X 1 0+X 2 0)+(203513409787/168600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (57/500 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (1404668890925042937/1405000000000000000 : ℝ)) (alpha := (203513409787/168600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1404668890925042937/1405000000000000000 : ℝ)*(X 0 1+X 2 1)+(203513409787/168600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (57/500 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (1404668890925042937/1405000000000000000 : ℝ)) (alpha := (203513409787/168600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1404668890925042937/1405000000000000000 : ℝ)*(X 0 2+X 1 2)+(203513409787/168600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (57/500 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (1404668890925042937/1405000000000000000 : ℝ)) (alpha := (203513409787/168600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-24338101/125000000 : ℝ)*X 0 0+(675831947/1250000000 : ℝ)*X 0 1+(1311888611/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346674337/10000000000 : ℝ)*X 1 0+(-2028028719/10000000000 : ℝ)*X 1 1+(5247554373/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1947059459/10000000000 : ℝ)*X 0 0+(5248129519/10000000000 : ℝ)*X 0 1+(5406077277/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s7_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5305193983/10000000000 : ℝ)*X 1 0+(-934752649/5000000000 : ℝ)*X 1 1+(5406077659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s7_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5305193469/10000000000 : ℝ)*X 2 0+(5406077701/10000000000 : ℝ)*X 2 1+(-373901189/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s7_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4296954189/10000000000 : ℝ)*X 0 0+(1118196547/2500000000 : ℝ)*X 0 1+(4127334403/10000000000 : ℝ)*X 0 2+(4296954189/10000000000 : ℝ)*X 1 0+(1118196547/2500000000 : ℝ)*X 1 1+(4127334403/10000000000 : ℝ)*X 1 2+(4296954189/10000000000 : ℝ)*X 2 0+(1118196547/2500000000 : ℝ)*X 2 1+(4127334403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5661559841229657555163881/3512500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1071587063/100000000000000 : ℝ)*(base19) + (2669807/1250000000000 : ℝ)*(base23) + (71736779/50000000000000 : ℝ)*(lower1) + (231507/800000000000 : ℝ)*(lower4) + (319263079/100000000000000 : ℝ)*(upper5) + (461297650300371/10000000000000 : ℝ)*(major0) + (461297650300371/10000000000000 : ℝ)*(major1) + (461297650300371/10000000000000 : ℝ)*(major2) + (999448913/100000000000000 : ℝ)*(sp0) + (19129707119/50000000000000 : ℝ)*(sp1) + (6331204318752307/100000000000000 : ℝ)*(sp2) + (6331165987199919/100000000000000 : ℝ)*(sp3) + (316560255230833/5000000000000 : ℝ)*(sp4) + (144737381703923/5000000000000 : ℝ)*(sp5) + (144737381703923/5000000000000 : ℝ)*(f.failure) + (316560265910061/5000000000000 : ℝ)*(f.sum) + (55918445709/8781250000000000000000000 : ℝ)*base66 + (123005923085545373/14050000000000000000000000000000 : ℝ)*base68 + (83352005200045373/14050000000000000000000000000000 : ℝ)*base70 + (41861789434645373/14050000000000000000000000000000 : ℝ)*base72 + (1268030873717/281000000000000000000000000 : ℝ)*base74 + (199682141225245373/14050000000000000000000000000000 : ℝ)*base76 + (12698632369504627/14050000000000000000000000000000 : ℝ)*base77 + (147796578203495373/14050000000000000000000000000000 : ℝ)*base80 + (1797456562421/281000000000000000000000000 : ℝ)*base82 + (729031/62500000000000000000 : ℝ)*base89 + (729031/62500000000000000000 : ℝ)*base91 + (729031/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1459_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1459_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1459_box_0 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-22356561/125000000 : ℝ)*x 0 + (2692482803/5000000000 : ℝ)*x 1 + (2692482999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22356561/125000000 : ℝ)^4419 ≤ (5321113296133/50000000000000 : ℝ)^3395 := by
    have hnat : (22356561 : ℕ)^4419*50000000000000^3395 ≤ 5321113296133^3395*125000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22356561 125000000 5321113296133 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692482803/5000000000 : ℝ)^4419 ≤ (4467888458539/10000000000000 : ℝ)^3395 := by
    have hnat : (2692482803 : ℕ)^4419*10000000000000^3395 ≤ 4467888458539^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692482803 5000000000 4467888458539 10000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692482999/5000000000 : ℝ)^4419 ≤ (22339444409397/50000000000000 : ℝ)^3395 := by
    have hnat : (2692482999 : ℕ)^4419*50000000000000^3395 ≤ 22339444409397^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692482999 5000000000 22339444409397 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22356561/125000000 : ℝ), (2692482803/5000000000 : ℝ), (2692482999/5000000000 : ℝ)] ![(5321113296133/50000000000000 : ℝ), (4467888458539/10000000000000 : ℝ), (22339444409397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22356561/125000000 : ℝ)|^4419 ≤ (5321113296133/50000000000000 : ℝ)^3395
        have hw : |(-22356561/125000000 : ℝ)|=(22356561/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692482803/5000000000 : ℝ)|^4419 ≤ (4467888458539/10000000000000 : ℝ)^3395
        have hw : |(2692482803/5000000000 : ℝ)|=(2692482803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692482999/5000000000 : ℝ)|^4419 ≤ (22339444409397/50000000000000 : ℝ)^3395
        have hw : |(2692482999/5000000000 : ℝ)|=(2692482999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_1 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528624673/1000000000 : ℝ)*x 0 + (-1924267331/10000000000 : ℝ)*x 1 + (2692483037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528624673/1000000000 : ℝ)^4419 ≤ (43615730335923/100000000000000 : ℝ)^3395 := by
    have hnat : (528624673 : ℕ)^4419*100000000000000^3395 ≤ 43615730335923^3395*1000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528624673 1000000000 43615730335923 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1924267331/10000000000 : ℝ)^4419 ≤ (11705380015417/100000000000000 : ℝ)^3395 := by
    have hnat : (1924267331 : ℕ)^4419*100000000000000^3395 ≤ 11705380015417^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924267331 10000000000 11705380015417 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692483037/5000000000 : ℝ)^4419 ≤ (11169722409889/25000000000000 : ℝ)^3395 := by
    have hnat : (2692483037 : ℕ)^4419*25000000000000^3395 ≤ 11169722409889^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692483037 5000000000 11169722409889 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528624673/1000000000 : ℝ), (-1924267331/10000000000 : ℝ), (2692483037/5000000000 : ℝ)] ![(43615730335923/100000000000000 : ℝ), (11705380015417/100000000000000 : ℝ), (11169722409889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528624673/1000000000 : ℝ)|^4419 ≤ (43615730335923/100000000000000 : ℝ)^3395
        have hw : |(528624673/1000000000 : ℝ)|=(528624673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1924267331/10000000000 : ℝ)|^4419 ≤ (11705380015417/100000000000000 : ℝ)^3395
        have hw : |(-1924267331/10000000000 : ℝ)|=(1924267331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692483037/5000000000 : ℝ)|^4419 ≤ (11169722409889/25000000000000 : ℝ)^3395
        have hw : |(2692483037/5000000000 : ℝ)|=(2692483037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_2 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286246873/10000000000 : ℝ)*x 0 + (2692482851/5000000000 : ℝ)*x 1 + (-481066911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286246873/10000000000 : ℝ)^4419 ≤ (43615731871657/100000000000000 : ℝ)^3395 := by
    have hnat : (5286246873 : ℕ)^4419*100000000000000^3395 ≤ 43615731871657^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286246873 10000000000 43615731871657 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692482851/5000000000 : ℝ)^4419 ≤ (22339442811071/50000000000000 : ℝ)^3395 := by
    have hnat : (2692482851 : ℕ)^4419*50000000000000^3395 ≤ 22339442811071^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692482851 5000000000 22339442811071 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481066911/2500000000 : ℝ)^4419 ≤ (1463172811711/12500000000000 : ℝ)^3395 := by
    have hnat : (481066911 : ℕ)^4419*12500000000000^3395 ≤ 1463172811711^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481066911 2500000000 1463172811711 12500000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286246873/10000000000 : ℝ), (2692482851/5000000000 : ℝ), (-481066911/2500000000 : ℝ)] ![(43615731871657/100000000000000 : ℝ), (22339442811071/50000000000000 : ℝ), (1463172811711/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286246873/10000000000 : ℝ)|^4419 ≤ (43615731871657/100000000000000 : ℝ)^3395
        have hw : |(5286246873/10000000000 : ℝ)|=(5286246873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692482851/5000000000 : ℝ)|^4419 ≤ (22339442811071/50000000000000 : ℝ)^3395
        have hw : |(2692482851/5000000000 : ℝ)|=(2692482851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-481066911/2500000000 : ℝ)|^4419 ≤ (1463172811711/12500000000000 : ℝ)^3395
        have hw : |(-481066911/2500000000 : ℝ)|=(481066911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_3 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2221321123/5000000000 : ℝ)*x 0 + (66058203/156250000 : ℝ)*x 1 + (2113862427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2221321123/5000000000 : ℝ)^4419 ≤ (34782669750821/100000000000000 : ℝ)^3395 := by
    have hnat : (2221321123 : ℕ)^4419*100000000000000^3395 ≤ 34782669750821^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221321123 5000000000 34782669750821 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66058203/156250000 : ℝ)^4419 ≤ (16304332905257/50000000000000 : ℝ)^3395 := by
    have hnat : (66058203 : ℕ)^4419*50000000000000^3395 ≤ 16304332905257^3395*156250000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66058203 156250000 16304332905257 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113862427/5000000000 : ℝ)^4419 ≤ (8152166106267/25000000000000 : ℝ)^3395 := by
    have hnat : (2113862427 : ℕ)^4419*25000000000000^3395 ≤ 8152166106267^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113862427 5000000000 8152166106267 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2221321123/5000000000 : ℝ), (66058203/156250000 : ℝ), (2113862427/5000000000 : ℝ)] ![(34782669750821/100000000000000 : ℝ), (16304332905257/50000000000000 : ℝ), (8152166106267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2221321123/5000000000 : ℝ)|^4419 ≤ (34782669750821/100000000000000 : ℝ)^3395
        have hw : |(2221321123/5000000000 : ℝ)|=(2221321123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66058203/156250000 : ℝ)|^4419 ≤ (16304332905257/50000000000000 : ℝ)^3395
        have hw : |(66058203/156250000 : ℝ)|=(66058203/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113862427/5000000000 : ℝ)|^4419 ≤ (8152166106267/25000000000000 : ℝ)^3395
        have hw : |(2113862427/5000000000 : ℝ)|=(2113862427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_4 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108305261/10000000000 : ℝ)*x 0 + (5266934023/10000000000 : ℝ)*x 1 + (2633467087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108305261/10000000000 : ℝ)^4419 ≤ (13183122649741/100000000000000 : ℝ)^3395 := by
    have hnat : (2108305261 : ℕ)^4419*100000000000000^3395 ≤ 13183122649741^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108305261 10000000000 13183122649741 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266934023/10000000000 : ℝ)^4419 ≤ (43408437858389/100000000000000 : ℝ)^3395 := by
    have hnat : (5266934023 : ℕ)^4419*100000000000000^3395 ≤ 43408437858389^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266934023 10000000000 43408437858389 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633467087/5000000000 : ℝ)^4419 ≤ (43408439478249/100000000000000 : ℝ)^3395 := by
    have hnat : (2633467087 : ℕ)^4419*100000000000000^3395 ≤ 43408439478249^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633467087 5000000000 43408439478249 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108305261/10000000000 : ℝ), (5266934023/10000000000 : ℝ), (2633467087/5000000000 : ℝ)] ![(13183122649741/100000000000000 : ℝ), (43408437858389/100000000000000 : ℝ), (43408439478249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108305261/10000000000 : ℝ)|^4419 ≤ (13183122649741/100000000000000 : ℝ)^3395
        have hw : |(-2108305261/10000000000 : ℝ)|=(2108305261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266934023/10000000000 : ℝ)|^4419 ≤ (43408437858389/100000000000000 : ℝ)^3395
        have hw : |(5266934023/10000000000 : ℝ)|=(5266934023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633467087/5000000000 : ℝ)|^4419 ≤ (43408439478249/100000000000000 : ℝ)^3395
        have hw : |(2633467087/5000000000 : ℝ)|=(2633467087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_5 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684375541/5000000000 : ℝ)*x 0 + (-1972373897/10000000000 : ℝ)*x 1 + (1053386821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684375541/5000000000 : ℝ)^4419 ≤ (44503855421161/100000000000000 : ℝ)^3395 := by
    have hnat : (2684375541 : ℕ)^4419*100000000000000^3395 ≤ 44503855421161^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684375541 5000000000 44503855421161 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972373897/10000000000 : ℝ)^4419 ≤ (6043852910507/50000000000000 : ℝ)^3395 := by
    have hnat : (1972373897 : ℕ)^4419*50000000000000^3395 ≤ 6043852910507^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972373897 10000000000 6043852910507 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053386821/2000000000 : ℝ)^4419 ≤ (339128427641/781250000000 : ℝ)^3395 := by
    have hnat : (1053386821 : ℕ)^4419*781250000000^3395 ≤ 339128427641^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053386821 2000000000 339128427641 781250000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684375541/5000000000 : ℝ), (-1972373897/10000000000 : ℝ), (1053386821/2000000000 : ℝ)] ![(44503855421161/100000000000000 : ℝ), (6043852910507/50000000000000 : ℝ), (339128427641/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684375541/5000000000 : ℝ)|^4419 ≤ (44503855421161/100000000000000 : ℝ)^3395
        have hw : |(2684375541/5000000000 : ℝ)|=(2684375541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1972373897/10000000000 : ℝ)|^4419 ≤ (6043852910507/50000000000000 : ℝ)^3395
        have hw : |(-1972373897/10000000000 : ℝ)|=(1972373897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053386821/2000000000 : ℝ)|^4419 ≤ (339128427641/781250000000 : ℝ)^3395
        have hw : |(1053386821/2000000000 : ℝ)|=(1053386821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_6 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368751283/10000000000 : ℝ)*x 0 + (2633467013/5000000000 : ℝ)*x 1 + (-493093433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368751283/10000000000 : ℝ)^4419 ≤ (44503857589887/100000000000000 : ℝ)^3395 := by
    have hnat : (5368751283 : ℕ)^4419*100000000000000^3395 ≤ 44503857589887^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368751283 10000000000 44503857589887 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633467013/5000000000 : ℝ)^4419 ≤ (43408437890571/100000000000000 : ℝ)^3395 := by
    have hnat : (2633467013 : ℕ)^4419*100000000000000^3395 ≤ 43408437890571^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633467013 5000000000 43408437890571 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493093433/2500000000 : ℝ)^4419 ≤ (12087704504811/100000000000000 : ℝ)^3395 := by
    have hnat : (493093433 : ℕ)^4419*100000000000000^3395 ≤ 12087704504811^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493093433 2500000000 12087704504811 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368751283/10000000000 : ℝ), (2633467013/5000000000 : ℝ), (-493093433/2500000000 : ℝ)] ![(44503857589887/100000000000000 : ℝ), (43408437890571/100000000000000 : ℝ), (12087704504811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368751283/10000000000 : ℝ)|^4419 ≤ (44503857589887/100000000000000 : ℝ)^3395
        have hw : |(5368751283/10000000000 : ℝ)|=(5368751283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633467013/5000000000 : ℝ)|^4419 ≤ (43408437890571/100000000000000 : ℝ)^3395
        have hw : |(2633467013/5000000000 : ℝ)|=(2633467013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-493093433/2500000000 : ℝ)|^4419 ≤ (12087704504811/100000000000000 : ℝ)^3395
        have hw : |(-493093433/2500000000 : ℝ)|=(493093433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_7 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4150128189/10000000000 : ℝ)*x 0 + (1093482979/2500000000 : ℝ)*x 1 + (4373931871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4150128189/10000000000 : ℝ)^4419 ≤ (7957950288461/25000000000000 : ℝ)^3395 := by
    have hnat : (4150128189 : ℕ)^4419*25000000000000^3395 ≤ 7957950288461^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150128189 10000000000 7957950288461 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093482979/2500000000 : ℝ)^4419 ≤ (17042049820893/50000000000000 : ℝ)^3395 := by
    have hnat : (1093482979 : ℕ)^4419*50000000000000^3395 ≤ 17042049820893^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093482979 2500000000 17042049820893 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4373931871/10000000000 : ℝ)^4419 ≤ (17042049592677/50000000000000 : ℝ)^3395 := by
    have hnat : (4373931871 : ℕ)^4419*50000000000000^3395 ≤ 17042049592677^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373931871 10000000000 17042049592677 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4150128189/10000000000 : ℝ), (1093482979/2500000000 : ℝ), (4373931871/10000000000 : ℝ)] ![(7957950288461/25000000000000 : ℝ), (17042049820893/50000000000000 : ℝ), (17042049592677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4150128189/10000000000 : ℝ)|^4419 ≤ (7957950288461/25000000000000 : ℝ)^3395
        have hw : |(4150128189/10000000000 : ℝ)|=(4150128189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093482979/2500000000 : ℝ)|^4419 ≤ (17042049820893/50000000000000 : ℝ)^3395
        have hw : |(1093482979/2500000000 : ℝ)|=(1093482979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4373931871/10000000000 : ℝ)|^4419 ≤ (17042049592677/50000000000000 : ℝ)^3395
        have hw : |(4373931871/10000000000 : ℝ)|=(4373931871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_8 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2040886731/10000000000 : ℝ)*x 0 + (1037032433/2000000000 : ℝ)*x 1 + (5398919673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040886731/10000000000 : ℝ)^4419 ≤ (12637071973951/100000000000000 : ℝ)^3395 := by
    have hnat : (2040886731 : ℕ)^4419*100000000000000^3395 ≤ 12637071973951^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040886731 10000000000 12637071973951 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037032433/2000000000 : ℝ)^4419 ≤ (8506657526691/20000000000000 : ℝ)^3395 := by
    have hnat : (1037032433 : ℕ)^4419*20000000000000^3395 ≤ 8506657526691^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037032433 2000000000 8506657526691 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398919673/10000000000 : ℝ)^4419 ≤ (8965928075003/20000000000000 : ℝ)^3395 := by
    have hnat : (5398919673 : ℕ)^4419*20000000000000^3395 ≤ 8965928075003^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398919673 10000000000 8965928075003 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2040886731/10000000000 : ℝ), (1037032433/2000000000 : ℝ), (5398919673/10000000000 : ℝ)] ![(12637071973951/100000000000000 : ℝ), (8506657526691/20000000000000 : ℝ), (8965928075003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2040886731/10000000000 : ℝ)|^4419 ≤ (12637071973951/100000000000000 : ℝ)^3395
        have hw : |(-2040886731/10000000000 : ℝ)|=(2040886731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037032433/2000000000 : ℝ)|^4419 ≤ (8506657526691/20000000000000 : ℝ)^3395
        have hw : |(1037032433/2000000000 : ℝ)|=(1037032433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398919673/10000000000 : ℝ)|^4419 ≤ (8965928075003/20000000000000 : ℝ)^3395
        have hw : |(5398919673/10000000000 : ℝ)|=(5398919673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_9 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276488219/10000000000 : ℝ)*x 0 + (-47961393/250000000 : ℝ)*x 1 + (5398921041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276488219/10000000000 : ℝ)^4419 ≤ (10877739747509/25000000000000 : ℝ)^3395 := by
    have hnat : (5276488219 : ℕ)^4419*25000000000000^3395 ≤ 10877739747509^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276488219 10000000000 10877739747509 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47961393/250000000 : ℝ)^4419 ≤ (2914846458927/25000000000000 : ℝ)^3395 := by
    have hnat : (47961393 : ℕ)^4419*25000000000000^3395 ≤ 2914846458927^3395*250000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47961393 250000000 2914846458927 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398921041/10000000000 : ℝ)^4419 ≤ (22414827580133/50000000000000 : ℝ)^3395 := by
    have hnat : (5398921041 : ℕ)^4419*50000000000000^3395 ≤ 22414827580133^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398921041 10000000000 22414827580133 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276488219/10000000000 : ℝ), (-47961393/250000000 : ℝ), (5398921041/10000000000 : ℝ)] ![(10877739747509/25000000000000 : ℝ), (2914846458927/25000000000000 : ℝ), (22414827580133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276488219/10000000000 : ℝ)|^4419 ≤ (10877739747509/25000000000000 : ℝ)^3395
        have hw : |(5276488219/10000000000 : ℝ)|=(5276488219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47961393/250000000 : ℝ)|^4419 ≤ (2914846458927/25000000000000 : ℝ)^3395
        have hw : |(-47961393/250000000 : ℝ)|=(47961393/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398921041/10000000000 : ℝ)|^4419 ≤ (22414827580133/50000000000000 : ℝ)^3395
        have hw : |(5398921041/10000000000 : ℝ)|=(5398921041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_10 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164890253/312500000 : ℝ)*x 0 + (84358141/156250000 : ℝ)*x 1 + (-1918455909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164890253/312500000 : ℝ)^4419 ≤ (21755478834913/50000000000000 : ℝ)^3395 := by
    have hnat : (164890253 : ℕ)^4419*50000000000000^3395 ≤ 21755478834913^3395*312500000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164890253 312500000 21755478834913 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84358141/156250000 : ℝ)^4419 ≤ (11207413744133/25000000000000 : ℝ)^3395 := by
    have hnat : (84358141 : ℕ)^4419*25000000000000^3395 ≤ 11207413744133^3395*156250000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84358141 156250000 11207413744133 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918455909/10000000000 : ℝ)^4419 ≤ (5829693665403/50000000000000 : ℝ)^3395 := by
    have hnat : (1918455909 : ℕ)^4419*50000000000000^3395 ≤ 5829693665403^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918455909 10000000000 5829693665403 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164890253/312500000 : ℝ), (84358141/156250000 : ℝ), (-1918455909/10000000000 : ℝ)] ![(21755478834913/50000000000000 : ℝ), (11207413744133/25000000000000 : ℝ), (5829693665403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164890253/312500000 : ℝ)|^4419 ≤ (21755478834913/50000000000000 : ℝ)^3395
        have hw : |(164890253/312500000 : ℝ)|=(164890253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84358141/156250000 : ℝ)|^4419 ≤ (11207413744133/25000000000000 : ℝ)^3395
        have hw : |(84358141/156250000 : ℝ)|=(84358141/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1918455909/10000000000 : ℝ)|^4419 ≤ (5829693665403/50000000000000 : ℝ)^3395
        have hw : |(-1918455909/10000000000 : ℝ)|=(1918455909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_11 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (895334171/2000000000 : ℝ)*x 0 + (210521209/500000000 : ℝ)*x 1 + (2105211549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895334171/2000000000 : ℝ)^4419 ≤ (8782461594523/25000000000000 : ℝ)^3395 := by
    have hnat : (895334171 : ℕ)^4419*25000000000000^3395 ≤ 8782461594523^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895334171 2000000000 8782461594523 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210521209/500000000 : ℝ)^4419 ≤ (32435082227947/100000000000000 : ℝ)^3395 := by
    have hnat : (210521209 : ℕ)^4419*100000000000000^3395 ≤ 32435082227947^3395*500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210521209 500000000 32435082227947 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2105211549/5000000000 : ℝ)^4419 ≤ (1297402855147/4000000000000 : ℝ)^3395 := by
    have hnat : (2105211549 : ℕ)^4419*4000000000000^3395 ≤ 1297402855147^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105211549 5000000000 1297402855147 4000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(895334171/2000000000 : ℝ), (210521209/500000000 : ℝ), (2105211549/5000000000 : ℝ)] ![(8782461594523/25000000000000 : ℝ), (32435082227947/100000000000000 : ℝ), (1297402855147/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(895334171/2000000000 : ℝ)|^4419 ≤ (8782461594523/25000000000000 : ℝ)^3395
        have hw : |(895334171/2000000000 : ℝ)|=(895334171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210521209/500000000 : ℝ)|^4419 ≤ (32435082227947/100000000000000 : ℝ)^3395
        have hw : |(210521209/500000000 : ℝ)|=(210521209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2105211549/5000000000 : ℝ)|^4419 ≤ (1297402855147/4000000000000 : ℝ)^3395
        have hw : |(2105211549/5000000000 : ℝ)|=(2105211549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_12 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-46401863/250000000 : ℝ)*x 0 + (54647723/100000000 : ℝ)*x 1 + (5255793949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46401863/250000000 : ℝ)^4419 ≤ (11168353056171/100000000000000 : ℝ)^3395 := by
    have hnat : (46401863 : ℕ)^4419*100000000000000^3395 ≤ 11168353056171^3395*250000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46401863 250000000 11168353056171 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54647723/100000000 : ℝ)^4419 ≤ (9108535324709/20000000000000 : ℝ)^3395 := by
    have hnat : (54647723 : ℕ)^4419*20000000000000^3395 ≤ 9108535324709^3395*100000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54647723 100000000 9108535324709 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255793949/10000000000 : ℝ)^4419 ≤ (43288970308501/100000000000000 : ℝ)^3395 := by
    have hnat : (5255793949 : ℕ)^4419*100000000000000^3395 ≤ 43288970308501^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255793949 10000000000 43288970308501 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46401863/250000000 : ℝ), (54647723/100000000 : ℝ), (5255793949/10000000000 : ℝ)] ![(11168353056171/100000000000000 : ℝ), (9108535324709/20000000000000 : ℝ), (43288970308501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46401863/250000000 : ℝ)|^4419 ≤ (11168353056171/100000000000000 : ℝ)^3395
        have hw : |(-46401863/250000000 : ℝ)|=(46401863/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54647723/100000000 : ℝ)|^4419 ≤ (9108535324709/20000000000000 : ℝ)^3395
        have hw : |(54647723/100000000 : ℝ)|=(54647723/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255793949/10000000000 : ℝ)|^4419 ≤ (43288970308501/100000000000000 : ℝ)^3395
        have hw : |(5255793949/10000000000 : ℝ)|=(5255793949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_13 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376536217/10000000000 : ℝ)*x 0 + (-1976815767/10000000000 : ℝ)*x 1 + (2627897263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376536217/10000000000 : ℝ)^4419 ≤ (1393371028277/3125000000000 : ℝ)^3395 := by
    have hnat : (5376536217 : ℕ)^4419*3125000000000^3395 ≤ 1393371028277^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376536217 10000000000 1393371028277 3125000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1976815767/10000000000 : ℝ)^4419 ≤ (6061575292953/50000000000000 : ℝ)^3395 := by
    have hnat : (1976815767 : ℕ)^4419*50000000000000^3395 ≤ 6061575292953^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976815767 10000000000 6061575292953 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627897263/5000000000 : ℝ)^4419 ≤ (8657795298869/20000000000000 : ℝ)^3395 := by
    have hnat : (2627897263 : ℕ)^4419*20000000000000^3395 ≤ 8657795298869^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627897263 5000000000 8657795298869 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376536217/10000000000 : ℝ), (-1976815767/10000000000 : ℝ), (2627897263/5000000000 : ℝ)] ![(1393371028277/3125000000000 : ℝ), (6061575292953/50000000000000 : ℝ), (8657795298869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376536217/10000000000 : ℝ)|^4419 ≤ (1393371028277/3125000000000 : ℝ)^3395
        have hw : |(5376536217/10000000000 : ℝ)|=(5376536217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1976815767/10000000000 : ℝ)|^4419 ≤ (6061575292953/50000000000000 : ℝ)^3395
        have hw : |(-1976815767/10000000000 : ℝ)|=(1976815767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627897263/5000000000 : ℝ)|^4419 ≤ (8657795298869/20000000000000 : ℝ)^3395
        have hw : |(2627897263/5000000000 : ℝ)|=(2627897263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_14 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376536469/10000000000 : ℝ)*x 0 + (525579397/1000000000 : ℝ)*x 1 + (-1976816173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376536469/10000000000 : ℝ)^4419 ≤ (11146968906263/25000000000000 : ℝ)^3395 := by
    have hnat : (5376536469 : ℕ)^4419*25000000000000^3395 ≤ 11146968906263^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376536469 10000000000 11146968906263 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525579397/1000000000 : ℝ)^4419 ≤ (10822242633409/25000000000000 : ℝ)^3395 := by
    have hnat : (525579397 : ℕ)^4419*25000000000000^3395 ≤ 10822242633409^3395*1000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525579397 1000000000 10822242633409 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1976816173/10000000000 : ℝ)^4419 ≤ (12123153826761/100000000000000 : ℝ)^3395 := by
    have hnat : (1976816173 : ℕ)^4419*100000000000000^3395 ≤ 12123153826761^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976816173 10000000000 12123153826761 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376536469/10000000000 : ℝ), (525579397/1000000000 : ℝ), (-1976816173/10000000000 : ℝ)] ![(11146968906263/25000000000000 : ℝ), (10822242633409/25000000000000 : ℝ), (12123153826761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376536469/10000000000 : ℝ)|^4419 ≤ (11146968906263/25000000000000 : ℝ)^3395
        have hw : |(5376536469/10000000000 : ℝ)|=(5376536469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525579397/1000000000 : ℝ)|^4419 ≤ (10822242633409/25000000000000 : ℝ)^3395
        have hw : |(525579397/1000000000 : ℝ)|=(525579397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1976816173/10000000000 : ℝ)|^4419 ≤ (12123153826761/100000000000000 : ℝ)^3395
        have hw : |(-1976816173/10000000000 : ℝ)|=(1976816173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_box_15 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (257629527/625000000 : ℝ)*x 0 + (4387718843/10000000000 : ℝ)*x 1 + (4387718447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257629527/625000000 : ℝ)^4419 ≤ (15775995901479/50000000000000 : ℝ)^3395 := by
    have hnat : (257629527 : ℕ)^4419*50000000000000^3395 ≤ 15775995901479^3395*625000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257629527 625000000 15775995901479 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4387718843/10000000000 : ℝ)^4419 ≤ (8556001524329/25000000000000 : ℝ)^3395 := by
    have hnat : (4387718843 : ℕ)^4419*25000000000000^3395 ≤ 8556001524329^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387718843 10000000000 8556001524329 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4387718447/10000000000 : ℝ)^4419 ≤ (6844800415379/20000000000000 : ℝ)^3395 := by
    have hnat : (4387718447 : ℕ)^4419*20000000000000^3395 ≤ 6844800415379^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387718447 10000000000 6844800415379 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(257629527/625000000 : ℝ), (4387718843/10000000000 : ℝ), (4387718447/10000000000 : ℝ)] ![(15775995901479/50000000000000 : ℝ), (8556001524329/25000000000000 : ℝ), (6844800415379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(257629527/625000000 : ℝ)|^4419 ≤ (15775995901479/50000000000000 : ℝ)^3395
        have hw : |(257629527/625000000 : ℝ)|=(257629527/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4387718843/10000000000 : ℝ)|^4419 ≤ (8556001524329/25000000000000 : ℝ)^3395
        have hw : |(4387718843/10000000000 : ℝ)|=(4387718843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4387718447/10000000000 : ℝ)|^4419 ≤ (6844800415379/20000000000000 : ℝ)^3395
        have hw : |(4387718447/10000000000 : ℝ)|=(4387718447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1459_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    -(62919/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29587/50000 : ℝ) ∧ (20153/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84797/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (57/500 : ℝ) ^ (2209/512 : ℝ) ≤ (8532183529706469/100000000000000000000 : ℝ) := by
    have hpowers : (57/500 : ℝ)^2209 ≤ (8532183529706469/100000000000000000000 : ℝ)^512 := by
      have hnat : (57 : ℕ)^2209*100000000000000000000^512 ≤ 8532183529706469^512*500^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57 500 8532183529706469 100000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57/500 : ℝ)) (X := (8532183529706469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14771/100000 : ℝ) ^ (2209/512 : ℝ) ≤ (26089030436829133/100000000000000000000 : ℝ) := by
    have hpowers : (14771/100000 : ℝ)^2209 ≤ (26089030436829133/100000000000000000000 : ℝ)^512 := by
      have hnat : (14771 : ℕ)^2209*100000000000000000000^512 ≤ 26089030436829133^512*100000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14771 100000 26089030436829133 100000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14771/100000 : ℝ)) (X := (26089030436829133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008532183529706469/50000000000000000000 : ℝ) ≤ (5000197745208677/5000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (50008532183529706469/50000000000000000000 : ℝ)^512 ≤ (5000197745208677/5000000000000000 : ℝ)^2209 := by
      have hnat : (50008532183529706469 : ℕ)^512*5000000000000000^2209 ≤ 5000197745208677^2209*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008532183529706469 50000000000000000000 5000197745208677 5000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000197745208677/5000000000000000 : ℝ)) (X := (50008532183529706469/50000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017310606983267801/50000000000000000000 : ℝ) ≤ (2500200585160191/2500000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (50017310606983267801/50000000000000000000 : ℝ)^512 ≤ (2500200585160191/2500000000000000 : ℝ)^2209 := by
      have hnat : (50017310606983267801 : ℕ)^512*2500000000000000^2209 ≤ 2500200585160191^2209*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017310606983267801 50000000000000000000 2500200585160191 2500000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500200585160191/2500000000000000 : ℝ)) (X := (50017310606983267801/50000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026089030436829133/50000000000000000000 : ℝ) ≤ (5000604595432087/5000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (50026089030436829133/50000000000000000000 : ℝ)^512 ≤ (5000604595432087/5000000000000000 : ℝ)^2209 := by
      have hnat : (50026089030436829133 : ℕ)^512*5000000000000000^2209 ≤ 5000604595432087^2209*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026089030436829133 50000000000000000000 5000604595432087 5000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000604595432087/5000000000000000 : ℝ)) (X := (50026089030436829133/50000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8532183529706469/100000000000000000000 : ℝ) ≤ ((16851028506551576167/16855000000000000000 : ℝ)+2*(40685022341/33710000000000 : ℝ)*(57/500 : ℝ))^(2209/512 : ℝ) := by
    rw [show (16851028506551576167/16855000000000000000 : ℝ)+2*(40685022341/33710000000000 : ℝ)*(57/500 : ℝ)=(5000197745208677/5000000000000000 : ℝ) by norm_num, show 1+2*(8532183529706469/100000000000000000000 : ℝ)=(50008532183529706469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26089030436829133/100000000000000000000 : ℝ)+(8532183529706469/100000000000000000000 : ℝ) ≤ ((16851028506551576167/16855000000000000000 : ℝ)+(40685022341/33710000000000 : ℝ)*((14771/100000 : ℝ)+(57/500 : ℝ)))^(2209/512 : ℝ) := by
    rw [show (16851028506551576167/16855000000000000000 : ℝ)+(40685022341/33710000000000 : ℝ)*((14771/100000 : ℝ)+(57/500 : ℝ))=(2500200585160191/2500000000000000 : ℝ) by norm_num, show 1+(26089030436829133/100000000000000000000 : ℝ)+(8532183529706469/100000000000000000000 : ℝ)=(50017310606983267801/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26089030436829133/100000000000000000000 : ℝ) ≤ ((16851028506551576167/16855000000000000000 : ℝ)+2*(40685022341/33710000000000 : ℝ)*(14771/100000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (16851028506551576167/16855000000000000000 : ℝ)+2*(40685022341/33710000000000 : ℝ)*(14771/100000 : ℝ)=(5000604595432087/5000000000000000 : ℝ) by norm_num, show 1+2*(26089030436829133/100000000000000000000 : ℝ)=(50026089030436829133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16851028506551576167/16855000000000000000 : ℝ)*(X 1 0+X 2 0)+(40685022341/33710000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16851028506551576167/16855000000000000000 : ℝ)) (alpha := (40685022341/33710000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16851028506551576167/16855000000000000000 : ℝ)*(X 0 1+X 2 1)+(40685022341/33710000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16851028506551576167/16855000000000000000 : ℝ)) (alpha := (40685022341/33710000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16851028506551576167/16855000000000000000 : ℝ)*(X 0 2+X 1 2)+(40685022341/33710000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16851028506551576167/16855000000000000000 : ℝ)) (alpha := (40685022341/33710000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-22356561/125000000 : ℝ)*X 0 0+(2692482803/5000000000 : ℝ)*X 0 1+(2692482999/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((528624673/1000000000 : ℝ)*X 1 0+(-1924267331/10000000000 : ℝ)*X 1 1+(2692483037/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286246873/10000000000 : ℝ)*X 2 0+(2692482851/5000000000 : ℝ)*X 2 1+(-481066911/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2221321123/5000000000 : ℝ)*X 0 0+(66058203/156250000 : ℝ)*X 0 1+(2113862427/5000000000 : ℝ)*X 0 2+(2221321123/5000000000 : ℝ)*X 1 0+(66058203/156250000 : ℝ)*X 1 1+(2113862427/5000000000 : ℝ)*X 1 2+(2221321123/5000000000 : ℝ)*X 2 0+(66058203/156250000 : ℝ)*X 2 1+(2113862427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108305261/10000000000 : ℝ)*X 0 0+(5266934023/10000000000 : ℝ)*X 0 1+(2633467087/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2684375541/5000000000 : ℝ)*X 1 0+(-1972373897/10000000000 : ℝ)*X 1 1+(1053386821/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5368751283/10000000000 : ℝ)*X 2 0+(2633467013/5000000000 : ℝ)*X 2 1+(-493093433/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4150128189/10000000000 : ℝ)*X 0 0+(1093482979/2500000000 : ℝ)*X 0 1+(4373931871/10000000000 : ℝ)*X 0 2+(4150128189/10000000000 : ℝ)*X 1 0+(1093482979/2500000000 : ℝ)*X 1 1+(4373931871/10000000000 : ℝ)*X 1 2+(4150128189/10000000000 : ℝ)*X 2 0+(1093482979/2500000000 : ℝ)*X 2 1+(4373931871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2040886731/10000000000 : ℝ)*X 0 0+(1037032433/2000000000 : ℝ)*X 0 1+(5398919673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276488219/10000000000 : ℝ)*X 1 0+(-47961393/250000000 : ℝ)*X 1 1+(5398921041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((164890253/312500000 : ℝ)*X 2 0+(84358141/156250000 : ℝ)*X 2 1+(-1918455909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((895334171/2000000000 : ℝ)*X 0 0+(210521209/500000000 : ℝ)*X 0 1+(2105211549/5000000000 : ℝ)*X 0 2+(895334171/2000000000 : ℝ)*X 1 0+(210521209/500000000 : ℝ)*X 1 1+(2105211549/5000000000 : ℝ)*X 1 2+(895334171/2000000000 : ℝ)*X 2 0+(210521209/500000000 : ℝ)*X 2 1+(2105211549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-46401863/250000000 : ℝ)*X 0 0+(54647723/100000000 : ℝ)*X 0 1+(5255793949/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5376536217/10000000000 : ℝ)*X 1 0+(-1976815767/10000000000 : ℝ)*X 1 1+(2627897263/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5376536469/10000000000 : ℝ)*X 2 0+(525579397/1000000000 : ℝ)*X 2 1+(-1976816173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((257629527/625000000 : ℝ)*X 0 0+(4387718843/10000000000 : ℝ)*X 0 1+(4387718447/10000000000 : ℝ)*X 0 2+(257629527/625000000 : ℝ)*X 1 0+(4387718843/10000000000 : ℝ)*X 1 1+(4387718447/10000000000 : ℝ)*X 1 2+(257629527/625000000 : ℝ)*X 2 0+(4387718843/10000000000 : ℝ)*X 2 1+(4387718447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62919/100000 : ℝ) ≤ (-26511435700022759565564654205767/42137500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2231403/12500000000000 : ℝ)*(upper0) + (18134853/20000000000000 : ℝ)*(lower2) + (568897/3125000000000 : ℝ)*(lower3) + (21159219/100000000000000 : ℝ)*(upper5) + (304934069853733/10000000000000 : ℝ)*(major0) + (304934069853733/10000000000000 : ℝ)*(major1) + (304934069853733/10000000000000 : ℝ)*(major2) + (229123187/25000000000000 : ℝ)*(sp1) + (21669593/12500000000000 : ℝ)*(sp2) + (1489654021/100000000000000 : ℝ)*(sp3) + (2103061471748459/50000000000000 : ℝ)*(sp4) + (420612202700417/10000000000000 : ℝ)*(sp5) + (2103061385070087/50000000000000 : ℝ)*(sp6) + (382705825408103/20000000000000 : ℝ)*(sp7) + (239191327086817/12500000000000 : ℝ)*(f.failure) + (2103061471748459/50000000000000 : ℝ)*(f.sum) + (6981809266953/3371000000000000000000000000 : ℝ)*base66 + (826983533649981411/168550000000000000000000000000000 : ℝ)*base67 + (1049661697009768589/168550000000000000000000000000000 : ℝ)*base70 + (743205308997268589/168550000000000000000000000000000 : ℝ)*base72 + (6857422199607/1685500000000000000000000000 : ℝ)*base74 + (1137202095378268589/168550000000000000000000000000000 : ℝ)*base76 + (1762271886354968589/168550000000000000000000000000000 : ℝ)*base78 + (162525260147918589/168550000000000000000000000000000 : ℝ)*base80 + (425779546983/674200000000000000000000000 : ℝ)*base81 + (527749/156250000000000000000 : ℝ)*base89 + (527749/156250000000000000000 : ℝ)*base91 + (527749/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29587/50000 : ℝ) ≤ (249354073911524391618517298682189/421375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1706293/4000000000000 : ℝ)*(upper1) + (92125153/100000000000000 : ℝ)*(upper2) + (39784319/100000000000000 : ℝ)*(upper3) + (4924073/25000000000000 : ℝ)*(upper4) + (1560980039373563/50000000000000 : ℝ)*(major0) + (1560980039373563/50000000000000 : ℝ)*(major1) + (1560980039373563/50000000000000 : ℝ)*(major2) + (2132542198250299/50000000000000 : ℝ)*(sp0) + (853016103859097/20000000000000 : ℝ)*(sp1) + (4265069363421557/100000000000000 : ℝ)*(sp2) + (979550464407967/50000000000000 : ℝ)*(sp3) + (13280812743/100000000000000 : ℝ)*(sp5) + (24436686671/100000000000000 : ℝ)*(sp10) + (940360763/10000000000000 : ℝ)*(sp12) + (979550464407967/50000000000000 : ℝ)*(f.failure) + (1066273450027057/25000000000000 : ℝ)*(f.sum) + (371695680117/210687500000000000000000000 : ℝ)*base66 + (10820671482756826979/842750000000000000000000000000000 : ℝ)*base68 + (25536112441550326979/842750000000000000000000000000000 : ℝ)*base70 + (7588721713432826979/842750000000000000000000000000000 : ℝ)*base72 + (733689506773/337100000000000000000000000 : ℝ)*base74 + (5639440795725576979/842750000000000000000000000000000 : ℝ)*base76 + (6054712515950576979/842750000000000000000000000000000 : ℝ)*base78 + (10225544802214326979/842750000000000000000000000000000 : ℝ)*base80 + (11695162578013/3371000000000000000000000000 : ℝ)*base81 + (8729299/625000000000000000000 : ℝ)*base89 + (8729299/625000000000000000000 : ℝ)*base91 + (8729299/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20153/25000 : ℝ) ≤ (108700865813269732550439573/134840000000000000000000000 : ℝ) := by norm_num
    linear_combination (18195481/12500000000000 : ℝ)*(upper0) + (113365281/50000000000000 : ℝ)*(upper1) + (35415587/12500000000000 : ℝ)*(upper3) + (380111/2500000000000 : ℝ)*(upper4) + (428519448151101/12500000000000 : ℝ)*(major0) + (428519448151101/12500000000000 : ℝ)*(major1) + (428519448151101/12500000000000 : ℝ)*(major2) + (52255839223/12500000000000 : ℝ)*(sp1) + (3940637813/800000000000 : ℝ)*(sp2) + (34489108851/25000000000000 : ℝ)*(sp3) + (4678194032043433/100000000000000 : ℝ)*(sp8) + (4677775985329649/100000000000000 : ℝ)*(sp9) + (584712681539601/12500000000000 : ℝ)*(sp10) + (430221522840179/20000000000000 : ℝ)*(sp11) + (2151245570636299/100000000000000 : ℝ)*(f.failure) + (4678194032043433/100000000000000 : ℝ)*(f.sum) + (66074426283/67420000000000000000000000 : ℝ)*base65 + (1435860176073277633/210687500000000000000000000000000 : ℝ)*base68 + (677337382616597367/210687500000000000000000000000000 : ℝ)*base69 + (2794784806144340133/210687500000000000000000000000000 : ℝ)*base72 + (2397858099777/842750000000000000000000000 : ℝ)*base74 + (567516267045597367/210687500000000000000000000000000 : ℝ)*base75 + (167907086963034867/210687500000000000000000000000000 : ℝ)*base77 + (1004514326297465133/210687500000000000000000000000000 : ℝ)*base80 + (4956015972161/1685500000000000000000000000 : ℝ)*base81 + (9651503/1250000000000000000000 : ℝ)*base89 + (9651503/1250000000000000000000 : ℝ)*base91 + (9651503/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84797/100000 : ℝ) ≤ (-89325208757878395867832120983903/105343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (141380097/50000000000000 : ℝ)*(upper3) + (2756393/10000000000000 : ℝ)*(lower4) + (86902399/100000000000000 : ℝ)*(upper5) + (433244261070301/12500000000000 : ℝ)*(major0) + (433244261070301/12500000000000 : ℝ)*(major1) + (433244261070301/12500000000000 : ℝ)*(major2) + (8207102129/50000000000000 : ℝ)*(sp0) + (196308443039/100000000000000 : ℝ)*(sp5) + (38660597309/10000000000000 : ℝ)*(sp6) + (14035881871/100000000000000 : ℝ)*(sp7) + (2392595724012581/50000000000000 : ℝ)*(sp12) + (239250577689319/5000000000000 : ℝ)*(sp13) + (4784821256256329/100000000000000 : ℝ)*(sp14) + (2174950954977637/100000000000000 : ℝ)*(sp15) + (543741247714877/25000000000000 : ℝ)*(f.failure) + (4785207862229419/100000000000000 : ℝ)*(f.sum) + (17590780788223/3371000000000000000000000000 : ℝ)*base65 + (2444630628918303767/210687500000000000000000000000000 : ℝ)*base67 + (1767170697679741267/210687500000000000000000000000000 : ℝ)*base69 + (2661610166574178767/210687500000000000000000000000000 : ℝ)*base71 + (428831341319/105343750000000000000000000 : ℝ)*base74 + (894895635532053767/210687500000000000000000000000000 : ℝ)*base75 + (2079355431891491267/210687500000000000000000000000000 : ℝ)*base77 + (3054669222501928767/210687500000000000000000000000000 : ℝ)*base79 + (20097638219963/3371000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4255431/312500000000000000000 : ℝ)*base90 + (4255431/312500000000000000000 : ℝ)*base92 + (4255431/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1459_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62919/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29587/50000 : ℝ) else (20153/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84797/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1459_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1459_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (591/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62919/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29587/50000 : ℝ) else (20153/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84797/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1459_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1459_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1459_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (591/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62919/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29587/50000 : ℝ) else (20153/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84797/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1459_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
