-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1071_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:11:00.759987+00:00
-- url     : https://prove2.me/submissions/093a2dae-0b90-42f7-b0ba-c9cf05df2ea2

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
theorem support_rectangle_w1071_s9_0 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-220131199/1000000000 : ℝ)*x 0 + (5394244243/10000000000 : ℝ)*x 1 + (1052913503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220131199/1000000000 : ℝ)^1033 ≤ (13369444857713/100000000000000 : ℝ)^777 := by
    have hnat : (220131199 : ℕ)^1033*100000000000000^777 ≤ 13369444857713^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220131199 1000000000 13369444857713 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394244243/10000000000 : ℝ)^1033 ≤ (22007928357359/50000000000000 : ℝ)^777 := by
    have hnat : (5394244243 : ℕ)^1033*50000000000000^777 ≤ 22007928357359^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394244243 10000000000 22007928357359 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052913503/2000000000 : ℝ)^1033 ≤ (42614698407247/100000000000000 : ℝ)^777 := by
    have hnat : (1052913503 : ℕ)^1033*100000000000000^777 ≤ 42614698407247^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052913503 2000000000 42614698407247 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220131199/1000000000 : ℝ), (5394244243/10000000000 : ℝ), (1052913503/2000000000 : ℝ)] ![(13369444857713/100000000000000 : ℝ), (22007928357359/50000000000000 : ℝ), (42614698407247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220131199/1000000000 : ℝ)|^1033 ≤ (13369444857713/100000000000000 : ℝ)^777
        have hw : |(-220131199/1000000000 : ℝ)|=(220131199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394244243/10000000000 : ℝ)|^1033 ≤ (22007928357359/50000000000000 : ℝ)^777
        have hw : |(5394244243/10000000000 : ℝ)|=(5394244243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052913503/2000000000 : ℝ)|^1033 ≤ (42614698407247/100000000000000 : ℝ)^777
        have hw : |(1052913503/2000000000 : ℝ)|=(1052913503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s9_1 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344960527/10000000000 : ℝ)*x 0 + (-2267104029/10000000000 : ℝ)*x 1 + (5264567789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344960527/10000000000 : ℝ)^1033 ≤ (43482023224469/100000000000000 : ℝ)^777 := by
    have hnat : (5344960527 : ℕ)^1033*100000000000000^777 ≤ 43482023224469^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344960527 10000000000 43482023224469 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2267104029/10000000000 : ℝ)^1033 ≤ (3475818850639/25000000000000 : ℝ)^777 := by
    have hnat : (2267104029 : ℕ)^1033*25000000000000^777 ≤ 3475818850639^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267104029 10000000000 3475818850639 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264567789/10000000000 : ℝ)^1033 ≤ (532683766949/1250000000000 : ℝ)^777 := by
    have hnat : (5264567789 : ℕ)^1033*1250000000000^777 ≤ 532683766949^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264567789 10000000000 532683766949 1250000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344960527/10000000000 : ℝ), (-2267104029/10000000000 : ℝ), (5264567789/10000000000 : ℝ)] ![(43482023224469/100000000000000 : ℝ), (3475818850639/25000000000000 : ℝ), (532683766949/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344960527/10000000000 : ℝ)|^1033 ≤ (43482023224469/100000000000000 : ℝ)^777
        have hw : |(5344960527/10000000000 : ℝ)|=(5344960527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2267104029/10000000000 : ℝ)|^1033 ≤ (3475818850639/25000000000000 : ℝ)^777
        have hw : |(-2267104029/10000000000 : ℝ)|=(2267104029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264567789/10000000000 : ℝ)|^1033 ≤ (532683766949/1250000000000 : ℝ)^777
        have hw : |(5264567789/10000000000 : ℝ)|=(5264567789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s9_2 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336240199/2500000000 : ℝ)*x 0 + (5264567541/10000000000 : ℝ)*x 1 + (-70847/312500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336240199/2500000000 : ℝ)^1033 ≤ (679406658341/1562500000000 : ℝ)^777 := by
    have hnat : (1336240199 : ℕ)^1033*1562500000000^777 ≤ 679406658341^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336240199 2500000000 679406658341 1562500000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264567541/10000000000 : ℝ)^1033 ≤ (5326837335881/12500000000000 : ℝ)^777 := by
    have hnat : (5264567541 : ℕ)^1033*12500000000000^777 ≤ 5326837335881^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264567541 10000000000 5326837335881 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70847/312500 : ℝ)^1033 ≤ (6951637583057/50000000000000 : ℝ)^777 := by
    have hnat : (70847 : ℕ)^1033*50000000000000^777 ≤ 6951637583057^777*312500^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70847 312500 6951637583057 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336240199/2500000000 : ℝ), (5264567541/10000000000 : ℝ), (-70847/312500 : ℝ)] ![(679406658341/1562500000000 : ℝ), (5326837335881/12500000000000 : ℝ), (6951637583057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336240199/2500000000 : ℝ)|^1033 ≤ (679406658341/1562500000000 : ℝ)^777
        have hw : |(1336240199/2500000000 : ℝ)|=(1336240199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264567541/10000000000 : ℝ)|^1033 ≤ (5326837335881/12500000000000 : ℝ)^777
        have hw : |(5264567541/10000000000 : ℝ)|=(5264567541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-70847/312500 : ℝ)|^1033 ≤ (6951637583057/50000000000000 : ℝ)^777
        have hw : |(-70847/312500 : ℝ)|=(70847/312500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s9_3 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4374774999/10000000000 : ℝ)*x 0 + (2124723053/5000000000 : ℝ)*x 1 + (70372593/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374774999/10000000000 : ℝ)^1033 ≤ (8329147929133/25000000000000 : ℝ)^777 := by
    have hnat : (4374774999 : ℕ)^1033*25000000000000^777 ≤ 8329147929133^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374774999 10000000000 8329147929133 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124723053/5000000000 : ℝ)^1033 ≤ (16026847905553/50000000000000 : ℝ)^777 := by
    have hnat : (2124723053 : ℕ)^1033*50000000000000^777 ≤ 16026847905553^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124723053 5000000000 16026847905553 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70372593/156250000 : ℝ)^1033 ≤ (34629712461843/100000000000000 : ℝ)^777 := by
    have hnat : (70372593 : ℕ)^1033*100000000000000^777 ≤ 34629712461843^777*156250000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70372593 156250000 34629712461843 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374774999/10000000000 : ℝ), (2124723053/5000000000 : ℝ), (70372593/156250000 : ℝ)] ![(8329147929133/25000000000000 : ℝ), (16026847905553/50000000000000 : ℝ), (34629712461843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374774999/10000000000 : ℝ)|^1033 ≤ (8329147929133/25000000000000 : ℝ)^777
        have hw : |(4374774999/10000000000 : ℝ)|=(4374774999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2124723053/5000000000 : ℝ)|^1033 ≤ (16026847905553/50000000000000 : ℝ)^777
        have hw : |(2124723053/5000000000 : ℝ)|=(2124723053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70372593/156250000 : ℝ)|^1033 ≤ (34629712461843/100000000000000 : ℝ)^777
        have hw : |(70372593/156250000 : ℝ)|=(70372593/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s9_4 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100658399/5000000000 : ℝ)*x 0 + (1316223161/2500000000 : ℝ)*x 1 + (2696959063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100658399/5000000000 : ℝ)^1033 ≤ (2673896735903/20000000000000 : ℝ)^777 := by
    have hnat : (1100658399 : ℕ)^1033*20000000000000^777 ≤ 2673896735903^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100658399 5000000000 2673896735903 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316223161/2500000000 : ℝ)^1033 ≤ (5327274668057/12500000000000 : ℝ)^777 := by
    have hnat : (1316223161 : ℕ)^1033*12500000000000^777 ≤ 5327274668057^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316223161 2500000000 5327274668057 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696959063/5000000000 : ℝ)^1033 ≤ (1375384967691/3125000000000 : ℝ)^777 := by
    have hnat : (2696959063 : ℕ)^1033*3125000000000^777 ≤ 1375384967691^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696959063 5000000000 1375384967691 3125000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100658399/5000000000 : ℝ), (1316223161/2500000000 : ℝ), (2696959063/5000000000 : ℝ)] ![(2673896735903/20000000000000 : ℝ), (5327274668057/12500000000000 : ℝ), (1375384967691/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100658399/5000000000 : ℝ)|^1033 ≤ (2673896735903/20000000000000 : ℝ)^777
        have hw : |(-1100658399/5000000000 : ℝ)|=(1100658399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316223161/2500000000 : ℝ)|^1033 ≤ (5327274668057/12500000000000 : ℝ)^777
        have hw : |(1316223161/2500000000 : ℝ)|=(1316223161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696959063/5000000000 : ℝ)|^1033 ≤ (1375384967691/3125000000000 : ℝ)^777
        have hw : |(2696959063/5000000000 : ℝ)|=(2696959063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s9_5 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2187391431/5000000000 : ℝ)*x 0 + (1125802533/2500000000 : ℝ)*x 1 + (4250086253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187391431/5000000000 : ℝ)^1033 ≤ (6663334265487/20000000000000 : ℝ)^777 := by
    have hnat : (2187391431 : ℕ)^1033*20000000000000^777 ≤ 6663334265487^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187391431 5000000000 6663334265487 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125802533/2500000000 : ℝ)^1033 ≤ (6924642625901/20000000000000 : ℝ)^777 := by
    have hnat : (1125802533 : ℕ)^1033*20000000000000^777 ≤ 6924642625901^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125802533 2500000000 6924642625901 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4250086253/10000000000 : ℝ)^1033 ≤ (16030057761809/50000000000000 : ℝ)^777 := by
    have hnat : (4250086253 : ℕ)^1033*50000000000000^777 ≤ 16030057761809^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250086253 10000000000 16030057761809 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187391431/5000000000 : ℝ), (1125802533/2500000000 : ℝ), (4250086253/10000000000 : ℝ)] ![(6663334265487/20000000000000 : ℝ), (6924642625901/20000000000000 : ℝ), (16030057761809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187391431/5000000000 : ℝ)|^1033 ≤ (6663334265487/20000000000000 : ℝ)^777
        have hw : |(2187391431/5000000000 : ℝ)|=(2187391431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125802533/2500000000 : ℝ)|^1033 ≤ (6924642625901/20000000000000 : ℝ)^777
        have hw : |(1125802533/2500000000 : ℝ)|=(1125802533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4250086253/10000000000 : ℝ)|^1033 ≤ (16030057761809/50000000000000 : ℝ)^777
        have hw : |(4250086253/10000000000 : ℝ)|=(4250086253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1071_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11259/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7003/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7003/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7003/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7003/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7003/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7003/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7003/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5629/50000 : ℝ) ^ (8263/2048 : ℝ) ≤ (14892275619852047/100000000000000000000 : ℝ) := by
    have hpowers : (5629/50000 : ℝ)^8263 ≤ (14892275619852047/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5629 : ℕ)^8263*100000000000000000000^2048 ≤ 14892275619852047^2048*50000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5629 50000 14892275619852047 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5629/50000 : ℝ)) (X := (14892275619852047/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7003/50000 : ℝ) ^ (8263/2048 : ℝ) ≤ (14378743088183/40000000000000000 : ℝ) := by
    have hpowers : (7003/50000 : ℝ)^8263 ≤ (14378743088183/40000000000000000 : ℝ)^2048 := by
      have hnat : (7003 : ℕ)^8263*40000000000000000^2048 ≤ 14378743088183^2048*50000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7003 50000 14378743088183 40000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7003/50000 : ℝ)) (X := (14378743088183/40000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014892275619852047/50000000000000000000 : ℝ) ≤ (10000738132996923/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50014892275619852047/50000000000000000000 : ℝ)^2048 ≤ (10000738132996923/10000000000000000 : ℝ)^8263 := by
      have hnat : (50014892275619852047 : ℕ)^2048*10000000000000000^8263 ≤ 10000738132996923^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014892275619852047 50000000000000000000 10000738132996923 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000738132996923/10000000000000000 : ℝ)) (X := (50014892275619852047/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050839133340309547/100000000000000000000 : ℝ) ≤ (10001259816583251/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (100050839133340309547/100000000000000000000 : ℝ)^2048 ≤ (10001259816583251/10000000000000000 : ℝ)^8263 := by
      have hnat : (100050839133340309547 : ℕ)^2048*10000000000000000^8263 ≤ 10001259816583251^8263*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050839133340309547 100000000000000000000 10001259816583251 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001259816583251/10000000000000000 : ℝ)) (X := (100050839133340309547/100000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (20014378743088183/20000000000000000 : ℝ) ≤ (10001781500169579/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (20014378743088183/20000000000000000 : ℝ)^2048 ≤ (10001781500169579/10000000000000000 : ℝ)^8263 := by
      have hnat : (20014378743088183 : ℕ)^2048*10000000000000000^8263 ≤ 10001781500169579^8263*20000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20014378743088183 20000000000000000 10001781500169579 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001781500169579/10000000000000000 : ℝ)) (X := (20014378743088183/20000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14892275619852047/100000000000000000000 : ℝ) ≤ ((2289190180153815263/2290000000000000000 : ℝ)+2*(21736816097/11450000000000 : ℝ)*(5629/50000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (2289190180153815263/2290000000000000000 : ℝ)+2*(21736816097/11450000000000 : ℝ)*(5629/50000 : ℝ)=(10000738132996923/10000000000000000 : ℝ) by norm_num, show 1+2*(14892275619852047/100000000000000000000 : ℝ)=(50014892275619852047/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14378743088183/40000000000000000 : ℝ)+(14892275619852047/100000000000000000000 : ℝ) ≤ ((2289190180153815263/2290000000000000000 : ℝ)+(21736816097/11450000000000 : ℝ)*((7003/50000 : ℝ)+(5629/50000 : ℝ)))^(8263/2048 : ℝ) := by
    rw [show (2289190180153815263/2290000000000000000 : ℝ)+(21736816097/11450000000000 : ℝ)*((7003/50000 : ℝ)+(5629/50000 : ℝ))=(10001259816583251/10000000000000000 : ℝ) by norm_num, show 1+(14378743088183/40000000000000000 : ℝ)+(14892275619852047/100000000000000000000 : ℝ)=(100050839133340309547/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14378743088183/40000000000000000 : ℝ) ≤ ((2289190180153815263/2290000000000000000 : ℝ)+2*(21736816097/11450000000000 : ℝ)*(7003/50000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (2289190180153815263/2290000000000000000 : ℝ)+2*(21736816097/11450000000000 : ℝ)*(7003/50000 : ℝ)=(10001781500169579/10000000000000000 : ℝ) by norm_num, show 1+2*(14378743088183/40000000000000000 : ℝ)=(20014378743088183/20000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2289190180153815263/2290000000000000000 : ℝ)*(X 1 0+X 2 0)+(21736816097/11450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (2289190180153815263/2290000000000000000 : ℝ)) (alpha := (21736816097/11450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2289190180153815263/2290000000000000000 : ℝ)*(X 0 1+X 2 1)+(21736816097/11450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (2289190180153815263/2290000000000000000 : ℝ)) (alpha := (21736816097/11450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2289190180153815263/2290000000000000000 : ℝ)*(X 0 2+X 1 2)+(21736816097/11450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (2289190180153815263/2290000000000000000 : ℝ)) (alpha := (21736816097/11450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-220131199/1000000000 : ℝ)*X 0 0+(5394244243/10000000000 : ℝ)*X 0 1+(1052913503/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344960527/10000000000 : ℝ)*X 1 0+(-2267104029/10000000000 : ℝ)*X 1 1+(5264567789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336240199/2500000000 : ℝ)*X 2 0+(5264567541/10000000000 : ℝ)*X 2 1+(-70847/312500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374774999/10000000000 : ℝ)*X 0 0+(2124723053/5000000000 : ℝ)*X 0 1+(70372593/156250000 : ℝ)*X 0 2+(4374774999/10000000000 : ℝ)*X 1 0+(2124723053/5000000000 : ℝ)*X 1 1+(70372593/156250000 : ℝ)*X 1 2+(4374774999/10000000000 : ℝ)*X 2 0+(2124723053/5000000000 : ℝ)*X 2 1+(70372593/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1100658399/5000000000 : ℝ)*X 0 0+(1316223161/2500000000 : ℝ)*X 0 1+(2696959063/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2187391431/5000000000 : ℝ)*X 0 0+(1125802533/2500000000 : ℝ)*X 0 1+(4250086253/10000000000 : ℝ)*X 0 2+(2187391431/5000000000 : ℝ)*X 1 0+(1125802533/2500000000 : ℝ)*X 1 1+(4250086253/10000000000 : ℝ)*X 1 2+(2187391431/5000000000 : ℝ)*X 2 0+(1125802533/2500000000 : ℝ)*X 2 1+(4250086253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5031849901556861340633/1145000000000000000000000000 : ℝ) := by norm_num
    linear_combination (211729827/25000000000000 : ℝ)*(base19) + (592537939/50000000000000 : ℝ)*(base23) + (13348707/50000000000000 : ℝ)*(lower2) + (51263571/50000000000000 : ℝ)*(upper3) + (92497819/50000000000000 : ℝ)*(upper5) + (1455299700829611/25000000000000 : ℝ)*(major0) + (1455299700829611/25000000000000 : ℝ)*(major1) + (1455299700829611/25000000000000 : ℝ)*(major2) + (3855757177865249/50000000000000 : ℝ)*(sp0) + (7711552922797901/100000000000000 : ℝ)*(sp1) + (7711552584641331/100000000000000 : ℝ)*(sp2) + (3930831483944209/100000000000000 : ℝ)*(sp3) + (39413986711/100000000000000 : ℝ)*(sp4) + (6103243919/50000000000000 : ℝ)*(sp5) + (245677730652003/6250000000000 : ℝ)*(f.failure) + (7711553769717209/100000000000000 : ℝ)*(f.sum) + (144872871469/1145000000000000000000000000 : ℝ)*base66 + (109545084594552693/57250000000000000000000000000000 : ℝ)*base67 + (256080617662052693/57250000000000000000000000000000 : ℝ)*base69 + (632355679173947307/57250000000000000000000000000000 : ℝ)*base72 + (779329842809/1145000000000000000000000000 : ℝ)*base74 + (952456281527197307/57250000000000000000000000000000 : ℝ)*base76 + (130626197420802693/57250000000000000000000000000000 : ℝ)*base77 + (345933635309697307/57250000000000000000000000000000 : ℝ)*base80 + (2498181175873/572500000000000000000000000 : ℝ)*base81 + (930189/125000000000000000000 : ℝ)*base89 + (930189/125000000000000000000 : ℝ)*base91 + (930189/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1071_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1071_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1071_box_0 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2072015907/10000000000 : ℝ)*x 0 + (2688650841/5000000000 : ℝ)*x 1 + (1344325347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072015907/10000000000 : ℝ)^1033 ≤ (1233569214873/10000000000000 : ℝ)^777 := by
    have hnat : (2072015907 : ℕ)^1033*10000000000000^777 ≤ 1233569214873^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072015907 10000000000 1233569214873 10000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688650841/5000000000 : ℝ)^1033 ≤ (8766431103443/20000000000000 : ℝ)^777 := by
    have hnat : (2688650841 : ℕ)^1033*20000000000000^777 ≤ 8766431103443^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688650841 5000000000 8766431103443 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344325347/2500000000 : ℝ)^1033 ≤ (21916076165573/50000000000000 : ℝ)^777 := by
    have hnat : (1344325347 : ℕ)^1033*50000000000000^777 ≤ 21916076165573^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344325347 2500000000 21916076165573 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2072015907/10000000000 : ℝ), (2688650841/5000000000 : ℝ), (1344325347/2500000000 : ℝ)] ![(1233569214873/10000000000000 : ℝ), (8766431103443/20000000000000 : ℝ), (21916076165573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2072015907/10000000000 : ℝ)|^1033 ≤ (1233569214873/10000000000000 : ℝ)^777
        have hw : |(-2072015907/10000000000 : ℝ)|=(2072015907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688650841/5000000000 : ℝ)|^1033 ≤ (8766431103443/20000000000000 : ℝ)^777
        have hw : |(2688650841/5000000000 : ℝ)|=(2688650841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344325347/2500000000 : ℝ)|^1033 ≤ (21916076165573/50000000000000 : ℝ)^777
        have hw : |(1344325347/2500000000 : ℝ)|=(1344325347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_1 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2647629557/5000000000 : ℝ)*x 0 + (-2183093267/10000000000 : ℝ)*x 1 + (5377301583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647629557/5000000000 : ℝ)^1033 ≤ (10736326321621/25000000000000 : ℝ)^777 := by
    have hnat : (2647629557 : ℕ)^1033*25000000000000^777 ≤ 10736326321621^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647629557 5000000000 10736326321621 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2183093267/10000000000 : ℝ)^1033 ≤ (6611270130323/50000000000000 : ℝ)^777 := by
    have hnat : (2183093267 : ℕ)^1033*50000000000000^777 ≤ 6611270130323^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183093267 10000000000 6611270130323 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377301583/10000000000 : ℝ)^1033 ≤ (8766430888871/20000000000000 : ℝ)^777 := by
    have hnat : (5377301583 : ℕ)^1033*20000000000000^777 ≤ 8766430888871^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377301583 10000000000 8766430888871 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647629557/5000000000 : ℝ), (-2183093267/10000000000 : ℝ), (5377301583/10000000000 : ℝ)] ![(10736326321621/25000000000000 : ℝ), (6611270130323/50000000000000 : ℝ), (8766430888871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647629557/5000000000 : ℝ)|^1033 ≤ (10736326321621/25000000000000 : ℝ)^777
        have hw : |(2647629557/5000000000 : ℝ)|=(2647629557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2183093267/10000000000 : ℝ)|^1033 ≤ (6611270130323/50000000000000 : ℝ)^777
        have hw : |(-2183093267/10000000000 : ℝ)|=(2183093267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377301583/10000000000 : ℝ)|^1033 ≤ (8766430888871/20000000000000 : ℝ)^777
        have hw : |(5377301583/10000000000 : ℝ)|=(5377301583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_2 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2647629641/5000000000 : ℝ)*x 0 + (2688650691/5000000000 : ℝ)*x 1 + (-34110833/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647629641/5000000000 : ℝ)^1033 ≤ (8589061419579/20000000000000 : ℝ)^777 := by
    have hnat : (2647629641 : ℕ)^1033*20000000000000^777 ≤ 8589061419579^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647629641 5000000000 8589061419579 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688650691/5000000000 : ℝ)^1033 ≤ (350657218129/800000000000 : ℝ)^777 := by
    have hnat : (2688650691 : ℕ)^1033*800000000000^777 ≤ 350657218129^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688650691 5000000000 350657218129 800000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34110833/156250000 : ℝ)^1033 ≤ (13222540623001/100000000000000 : ℝ)^777 := by
    have hnat : (34110833 : ℕ)^1033*100000000000000^777 ≤ 13222540623001^777*156250000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34110833 156250000 13222540623001 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647629641/5000000000 : ℝ), (2688650691/5000000000 : ℝ), (-34110833/156250000 : ℝ)] ![(8589061419579/20000000000000 : ℝ), (350657218129/800000000000 : ℝ), (13222540623001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647629641/5000000000 : ℝ)|^1033 ≤ (8589061419579/20000000000000 : ℝ)^777
        have hw : |(2647629641/5000000000 : ℝ)|=(2647629641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688650691/5000000000 : ℝ)|^1033 ≤ (350657218129/800000000000 : ℝ)^777
        have hw : |(2688650691/5000000000 : ℝ)|=(2688650691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34110833/156250000 : ℝ)|^1033 ≤ (13222540623001/100000000000000 : ℝ)^777
        have hw : |(-34110833/156250000 : ℝ)|=(34110833/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_3 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2241553689/5000000000 : ℝ)*x 0 + (432276723/1000000000 : ℝ)*x 1 + (4322767237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2241553689/5000000000 : ℝ)^1033 ≤ (6883575888919/20000000000000 : ℝ)^777 := by
    have hnat : (2241553689 : ℕ)^1033*20000000000000^777 ≤ 6883575888919^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241553689 5000000000 6883575888919 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432276723/1000000000 : ℝ)^1033 ≤ (32791060231671/100000000000000 : ℝ)^777 := by
    have hnat : (432276723 : ℕ)^1033*100000000000000^777 ≤ 32791060231671^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432276723 1000000000 32791060231671 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4322767237/10000000000 : ℝ)^1033 ≤ (6558212060453/20000000000000 : ℝ)^777 := by
    have hnat : (4322767237 : ℕ)^1033*20000000000000^777 ≤ 6558212060453^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322767237 10000000000 6558212060453 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2241553689/5000000000 : ℝ), (432276723/1000000000 : ℝ), (4322767237/10000000000 : ℝ)] ![(6883575888919/20000000000000 : ℝ), (32791060231671/100000000000000 : ℝ), (6558212060453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2241553689/5000000000 : ℝ)|^1033 ≤ (6883575888919/20000000000000 : ℝ)^777
        have hw : |(2241553689/5000000000 : ℝ)|=(2241553689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(432276723/1000000000 : ℝ)|^1033 ≤ (32791060231671/100000000000000 : ℝ)^777
        have hw : |(432276723/1000000000 : ℝ)|=(432276723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4322767237/10000000000 : ℝ)|^1033 ≤ (6558212060453/20000000000000 : ℝ)^777
        have hw : |(4322767237/10000000000 : ℝ)|=(4322767237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_4 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2331987423/10000000000 : ℝ)*x 0 + (264008193/500000000 : ℝ)*x 1 + (2640081913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2331987423/10000000000 : ℝ)^1033 ≤ (3608689301019/25000000000000 : ℝ)^777 := by
    have hnat : (2331987423 : ℕ)^1033*25000000000000^777 ≤ 3608689301019^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2331987423 10000000000 3608689301019 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264008193/500000000 : ℝ)^1033 ≤ (42782621573307/100000000000000 : ℝ)^777 := by
    have hnat : (264008193 : ℕ)^1033*100000000000000^777 ≤ 42782621573307^777*500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264008193 500000000 42782621573307 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640081913/5000000000 : ℝ)^1033 ≤ (42782621207057/100000000000000 : ℝ)^777 := by
    have hnat : (2640081913 : ℕ)^1033*100000000000000^777 ≤ 42782621207057^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640081913 5000000000 42782621207057 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2331987423/10000000000 : ℝ), (264008193/500000000 : ℝ), (2640081913/5000000000 : ℝ)] ![(3608689301019/25000000000000 : ℝ), (42782621573307/100000000000000 : ℝ), (42782621207057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2331987423/10000000000 : ℝ)|^1033 ≤ (3608689301019/25000000000000 : ℝ)^777
        have hw : |(-2331987423/10000000000 : ℝ)|=(2331987423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264008193/500000000 : ℝ)|^1033 ≤ (42782621573307/100000000000000 : ℝ)^777
        have hw : |(264008193/500000000 : ℝ)|=(264008193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640081913/5000000000 : ℝ)|^1033 ≤ (42782621207057/100000000000000 : ℝ)^777
        have hw : |(2640081913/5000000000 : ℝ)|=(2640081913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_5 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (107279949/200000000 : ℝ)*x 0 + (-8884343/40000000 : ℝ)*x 1 + (2640081903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107279949/200000000 : ℝ)^1033 ≤ (10922009199509/25000000000000 : ℝ)^777 := by
    have hnat : (107279949 : ℕ)^1033*25000000000000^777 ≤ 10922009199509^777*200000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107279949 200000000 10922009199509 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8884343/40000000 : ℝ)^1033 ≤ (13529342197169/100000000000000 : ℝ)^777 := by
    have hnat : (8884343 : ℕ)^1033*100000000000000^777 ≤ 13529342197169^777*40000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8884343 40000000 13529342197169 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640081903/5000000000 : ℝ)^1033 ≤ (8556524198323/20000000000000 : ℝ)^777 := by
    have hnat : (2640081903 : ℕ)^1033*20000000000000^777 ≤ 8556524198323^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640081903 5000000000 8556524198323 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107279949/200000000 : ℝ), (-8884343/40000000 : ℝ), (2640081903/5000000000 : ℝ)] ![(10922009199509/25000000000000 : ℝ), (13529342197169/100000000000000 : ℝ), (8556524198323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107279949/200000000 : ℝ)|^1033 ≤ (10922009199509/25000000000000 : ℝ)^777
        have hw : |(107279949/200000000 : ℝ)|=(107279949/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8884343/40000000 : ℝ)|^1033 ≤ (13529342197169/100000000000000 : ℝ)^777
        have hw : |(-8884343/40000000 : ℝ)|=(8884343/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640081903/5000000000 : ℝ)|^1033 ≤ (8556524198323/20000000000000 : ℝ)^777
        have hw : |(2640081903/5000000000 : ℝ)|=(2640081903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_6 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5363997373/10000000000 : ℝ)*x 0 + (330010249/625000000 : ℝ)*x 1 + (-138817851/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363997373/10000000000 : ℝ)^1033 ≤ (4368803596427/10000000000000 : ℝ)^777 := by
    have hnat : (5363997373 : ℕ)^1033*10000000000000^777 ≤ 4368803596427^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363997373 10000000000 4368803596427 10000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330010249/625000000 : ℝ)^1033 ≤ (10695655727261/25000000000000 : ℝ)^777 := by
    have hnat : (330010249 : ℕ)^1033*25000000000000^777 ≤ 10695655727261^777*625000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330010249 625000000 10695655727261 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138817851/625000000 : ℝ)^1033 ≤ (2705868222401/20000000000000 : ℝ)^777 := by
    have hnat : (138817851 : ℕ)^1033*20000000000000^777 ≤ 2705868222401^777*625000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138817851 625000000 2705868222401 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363997373/10000000000 : ℝ), (330010249/625000000 : ℝ), (-138817851/625000000 : ℝ)] ![(4368803596427/10000000000000 : ℝ), (10695655727261/25000000000000 : ℝ), (2705868222401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363997373/10000000000 : ℝ)|^1033 ≤ (4368803596427/10000000000000 : ℝ)^777
        have hw : |(5363997373/10000000000 : ℝ)|=(5363997373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(330010249/625000000 : ℝ)|^1033 ≤ (10695655727261/25000000000000 : ℝ)^777
        have hw : |(330010249/625000000 : ℝ)|=(330010249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-138817851/625000000 : ℝ)|^1033 ≤ (2705868222401/20000000000000 : ℝ)^777
        have hw : |(-138817851/625000000 : ℝ)|=(138817851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_7 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4266111431/10000000000 : ℝ)*x 0 + (4431243817/10000000000 : ℝ)*x 1 + (886248753/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266111431/10000000000 : ℝ)^1033 ≤ (32220927708981/100000000000000 : ℝ)^777 := by
    have hnat : (4266111431 : ℕ)^1033*100000000000000^777 ≤ 32220927708981^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266111431 10000000000 32220927708981 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4431243817/10000000000 : ℝ)^1033 ≤ (16944768202519/50000000000000 : ℝ)^777 := by
    have hnat : (4431243817 : ℕ)^1033*50000000000000^777 ≤ 16944768202519^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431243817 10000000000 16944768202519 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886248753/2000000000 : ℝ)^1033 ≤ (16944767938161/50000000000000 : ℝ)^777 := by
    have hnat : (886248753 : ℕ)^1033*50000000000000^777 ≤ 16944767938161^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886248753 2000000000 16944767938161 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266111431/10000000000 : ℝ), (4431243817/10000000000 : ℝ), (886248753/2000000000 : ℝ)] ![(32220927708981/100000000000000 : ℝ), (16944768202519/50000000000000 : ℝ), (16944767938161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266111431/10000000000 : ℝ)|^1033 ≤ (32220927708981/100000000000000 : ℝ)^777
        have hw : |(4266111431/10000000000 : ℝ)|=(4266111431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4431243817/10000000000 : ℝ)|^1033 ≤ (16944768202519/50000000000000 : ℝ)^777
        have hw : |(4431243817/10000000000 : ℝ)|=(4431243817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(886248753/2000000000 : ℝ)|^1033 ≤ (16944767938161/50000000000000 : ℝ)^777
        have hw : |(886248753/2000000000 : ℝ)|=(886248753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_8 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-569427441/2500000000 : ℝ)*x 0 + (325890013/625000000 : ℝ)*x 1 + (2693451539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (569427441/2500000000 : ℝ)^1033 ≤ (6994906014733/50000000000000 : ℝ)^777 := by
    have hnat : (569427441 : ℕ)^1033*50000000000000^777 ≤ 6994906014733^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569427441 2500000000 6994906014733 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325890013/625000000 : ℝ)^1033 ≤ (42073951839411/100000000000000 : ℝ)^777 := by
    have hnat : (325890013 : ℕ)^1033*100000000000000^777 ≤ 42073951839411^777*625000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325890013 625000000 42073951839411 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693451539/5000000000 : ℝ)^1033 ≤ (2746014757307/6250000000000 : ℝ)^777 := by
    have hnat : (2693451539 : ℕ)^1033*6250000000000^777 ≤ 2746014757307^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693451539 5000000000 2746014757307 6250000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-569427441/2500000000 : ℝ), (325890013/625000000 : ℝ), (2693451539/5000000000 : ℝ)] ![(6994906014733/50000000000000 : ℝ), (42073951839411/100000000000000 : ℝ), (2746014757307/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-569427441/2500000000 : ℝ)|^1033 ≤ (6994906014733/50000000000000 : ℝ)^777
        have hw : |(-569427441/2500000000 : ℝ)|=(569427441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325890013/625000000 : ℝ)|^1033 ≤ (42073951839411/100000000000000 : ℝ)^777
        have hw : |(325890013/625000000 : ℝ)|=(325890013/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693451539/5000000000 : ℝ)|^1033 ≤ (2746014757307/6250000000000 : ℝ)^777
        have hw : |(2693451539/5000000000 : ℝ)|=(2693451539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_9 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5288461429/10000000000 : ℝ)*x 0 + (-1089633173/5000000000 : ℝ)*x 1 + (2693451707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288461429/10000000000 : ℝ)^1033 ≤ (2143601336233/5000000000000 : ℝ)^777 := by
    have hnat : (5288461429 : ℕ)^1033*5000000000000^777 ≤ 2143601336233^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288461429 10000000000 2143601336233 5000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089633173/5000000000 : ℝ)^1033 ≤ (13191733507751/100000000000000 : ℝ)^777 := by
    have hnat : (1089633173 : ℕ)^1033*100000000000000^777 ≤ 13191733507751^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089633173 5000000000 13191733507751 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693451707/5000000000 : ℝ)^1033 ≤ (21968119880137/50000000000000 : ℝ)^777 := by
    have hnat : (2693451707 : ℕ)^1033*50000000000000^777 ≤ 21968119880137^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693451707 5000000000 21968119880137 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288461429/10000000000 : ℝ), (-1089633173/5000000000 : ℝ), (2693451707/5000000000 : ℝ)] ![(2143601336233/5000000000000 : ℝ), (13191733507751/100000000000000 : ℝ), (21968119880137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288461429/10000000000 : ℝ)|^1033 ≤ (2143601336233/5000000000000 : ℝ)^777
        have hw : |(5288461429/10000000000 : ℝ)|=(5288461429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1089633173/5000000000 : ℝ)|^1033 ≤ (13191733507751/100000000000000 : ℝ)^777
        have hw : |(-1089633173/5000000000 : ℝ)|=(1089633173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693451707/5000000000 : ℝ)|^1033 ≤ (21968119880137/50000000000000 : ℝ)^777
        have hw : |(2693451707/5000000000 : ℝ)|=(2693451707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_10 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5288461387/10000000000 : ℝ)*x 0 + (5386902421/10000000000 : ℝ)*x 1 + (-108963387/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288461387/10000000000 : ℝ)^1033 ≤ (42872026271999/100000000000000 : ℝ)^777 := by
    have hnat : (5288461387 : ℕ)^1033*100000000000000^777 ≤ 42872026271999^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288461387 10000000000 42872026271999 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386902421/10000000000 : ℝ)^1033 ≤ (1098405724821/2500000000000 : ℝ)^777 := by
    have hnat : (5386902421 : ℕ)^1033*2500000000000^777 ≤ 1098405724821^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386902421 10000000000 1098405724821 2500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108963387/500000000 : ℝ)^1033 ≤ (13191744726223/100000000000000 : ℝ)^777 := by
    have hnat : (108963387 : ℕ)^1033*100000000000000^777 ≤ 13191744726223^777*500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108963387 500000000 13191744726223 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288461387/10000000000 : ℝ), (5386902421/10000000000 : ℝ), (-108963387/500000000 : ℝ)] ![(42872026271999/100000000000000 : ℝ), (1098405724821/2500000000000 : ℝ), (13191744726223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288461387/10000000000 : ℝ)|^1033 ≤ (42872026271999/100000000000000 : ℝ)^777
        have hw : |(5288461387/10000000000 : ℝ)|=(5288461387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386902421/10000000000 : ℝ)|^1033 ≤ (1098405724821/2500000000000 : ℝ)^777
        have hw : |(5386902421/10000000000 : ℝ)|=(5386902421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108963387/500000000 : ℝ)|^1033 ≤ (13191744726223/100000000000000 : ℝ)^777
        have hw : |(-108963387/500000000 : ℝ)|=(108963387/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_11 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2252141667/5000000000 : ℝ)*x 0 + (4312038001/10000000000 : ℝ)*x 1 + (53900493/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2252141667/5000000000 : ℝ)^1033 ≤ (17317091771301/50000000000000 : ℝ)^777 := by
    have hnat : (2252141667 : ℕ)^1033*50000000000000^777 ≤ 17317091771301^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252141667 5000000000 17317091771301 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4312038001/10000000000 : ℝ)^1033 ≤ (32682900969317/100000000000000 : ℝ)^777 := by
    have hnat : (4312038001 : ℕ)^1033*100000000000000^777 ≤ 32682900969317^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312038001 10000000000 32682900969317 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53900493/125000000 : ℝ)^1033 ≤ (4085364433707/12500000000000 : ℝ)^777 := by
    have hnat : (53900493 : ℕ)^1033*12500000000000^777 ≤ 4085364433707^777*125000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53900493 125000000 4085364433707 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2252141667/5000000000 : ℝ), (4312038001/10000000000 : ℝ), (53900493/125000000 : ℝ)] ![(17317091771301/50000000000000 : ℝ), (32682900969317/100000000000000 : ℝ), (4085364433707/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2252141667/5000000000 : ℝ)|^1033 ≤ (17317091771301/50000000000000 : ℝ)^777
        have hw : |(2252141667/5000000000 : ℝ)|=(2252141667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4312038001/10000000000 : ℝ)|^1033 ≤ (32682900969317/100000000000000 : ℝ)^777
        have hw : |(4312038001/10000000000 : ℝ)|=(4312038001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53900493/125000000 : ℝ)|^1033 ≤ (4085364433707/12500000000000 : ℝ)^777
        have hw : |(53900493/125000000 : ℝ)|=(53900493/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_12 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2126658743/10000000000 : ℝ)*x 0 + (5441893823/10000000000 : ℝ)*x 1 + (2636079917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126658743/10000000000 : ℝ)^1033 ≤ (6385028501471/50000000000000 : ℝ)^777 := by
    have hnat : (2126658743 : ℕ)^1033*50000000000000^777 ≤ 6385028501471^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126658743 10000000000 6385028501471 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441893823/10000000000 : ℝ)^1033 ≤ (44533519815203/100000000000000 : ℝ)^777 := by
    have hnat : (5441893823 : ℕ)^1033*100000000000000^777 ≤ 44533519815203^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441893823 10000000000 44533519815203 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636079917/5000000000 : ℝ)^1033 ≤ (42696423157391/100000000000000 : ℝ)^777 := by
    have hnat : (2636079917 : ℕ)^1033*100000000000000^777 ≤ 42696423157391^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636079917 5000000000 42696423157391 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2126658743/10000000000 : ℝ), (5441893823/10000000000 : ℝ), (2636079917/5000000000 : ℝ)] ![(6385028501471/50000000000000 : ℝ), (44533519815203/100000000000000 : ℝ), (42696423157391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2126658743/10000000000 : ℝ)|^1033 ≤ (6385028501471/50000000000000 : ℝ)^777
        have hw : |(-2126658743/10000000000 : ℝ)|=(2126658743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441893823/10000000000 : ℝ)|^1033 ≤ (44533519815203/100000000000000 : ℝ)^777
        have hw : |(5441893823/10000000000 : ℝ)|=(5441893823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636079917/5000000000 : ℝ)|^1033 ≤ (42696423157391/100000000000000 : ℝ)^777
        have hw : |(2636079917/5000000000 : ℝ)|=(2636079917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_13 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2684829573/5000000000 : ℝ)*x 0 + (-278019677/1250000000 : ℝ)*x 1 + (2636079957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684829573/5000000000 : ℝ)^1033 ≤ (21874676504247/50000000000000 : ℝ)^777 := by
    have hnat : (2684829573 : ℕ)^1033*50000000000000^777 ≤ 21874676504247^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684829573 5000000000 21874676504247 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278019677/1250000000 : ℝ)^1033 ≤ (6777111475933/50000000000000 : ℝ)^777 := by
    have hnat : (278019677 : ℕ)^1033*50000000000000^777 ≤ 6777111475933^777*1250000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278019677 1250000000 6777111475933 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636079957/5000000000 : ℝ)^1033 ≤ (21348212009363/50000000000000 : ℝ)^777 := by
    have hnat : (2636079957 : ℕ)^1033*50000000000000^777 ≤ 21348212009363^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636079957 5000000000 21348212009363 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684829573/5000000000 : ℝ), (-278019677/1250000000 : ℝ), (2636079957/5000000000 : ℝ)] ![(21874676504247/50000000000000 : ℝ), (6777111475933/50000000000000 : ℝ), (21348212009363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684829573/5000000000 : ℝ)|^1033 ≤ (21874676504247/50000000000000 : ℝ)^777
        have hw : |(2684829573/5000000000 : ℝ)|=(2684829573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-278019677/1250000000 : ℝ)|^1033 ≤ (6777111475933/50000000000000 : ℝ)^777
        have hw : |(-278019677/1250000000 : ℝ)|=(278019677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636079957/5000000000 : ℝ)|^1033 ≤ (21348212009363/50000000000000 : ℝ)^777
        have hw : |(2636079957/5000000000 : ℝ)|=(2636079957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_14 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2684829633/5000000000 : ℝ)*x 0 + (1054431937/2000000000 : ℝ)*x 1 + (-55603939/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684829633/5000000000 : ℝ)^1033 ≤ (43749354308321/100000000000000 : ℝ)^777 := by
    have hnat : (2684829633 : ℕ)^1033*100000000000000^777 ≤ 43749354308321^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684829633 5000000000 43749354308321 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054431937/2000000000 : ℝ)^1033 ≤ (21348210776577/50000000000000 : ℝ)^777 := by
    have hnat : (1054431937 : ℕ)^1033*50000000000000^777 ≤ 21348210776577^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054431937 2000000000 21348210776577 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55603939/250000000 : ℝ)^1033 ≤ (847139007409/6250000000000 : ℝ)^777 := by
    have hnat : (55603939 : ℕ)^1033*6250000000000^777 ≤ 847139007409^777*250000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55603939 250000000 847139007409 6250000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684829633/5000000000 : ℝ), (1054431937/2000000000 : ℝ), (-55603939/250000000 : ℝ)] ![(43749354308321/100000000000000 : ℝ), (21348210776577/50000000000000 : ℝ), (847139007409/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684829633/5000000000 : ℝ)|^1033 ≤ (43749354308321/100000000000000 : ℝ)^777
        have hw : |(2684829633/5000000000 : ℝ)|=(2684829633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054431937/2000000000 : ℝ)|^1033 ≤ (21348210776577/50000000000000 : ℝ)^777
        have hw : |(1054431937/2000000000 : ℝ)|=(1054431937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55603939/250000000 : ℝ)|^1033 ≤ (847139007409/6250000000000 : ℝ)^777
        have hw : |(-55603939/250000000 : ℝ)|=(55603939/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_box_15 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4248001637/10000000000 : ℝ)*x 0 + (4440176579/10000000000 : ℝ)*x 1 + (4440177159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248001637/10000000000 : ℝ)^1033 ≤ (8009802782049/25000000000000 : ℝ)^777 := by
    have hnat : (4248001637 : ℕ)^1033*25000000000000^777 ≤ 8009802782049^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248001637 10000000000 8009802782049 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4440176579/10000000000 : ℝ)^1033 ≤ (2123774467367/6250000000000 : ℝ)^777 := by
    have hnat : (4440176579 : ℕ)^1033*6250000000000^777 ≤ 2123774467367^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4440176579 10000000000 2123774467367 6250000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4440177159/10000000000 : ℝ)^1033 ≤ (6796079475801/20000000000000 : ℝ)^777 := by
    have hnat : (4440177159 : ℕ)^1033*20000000000000^777 ≤ 6796079475801^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4440177159 10000000000 6796079475801 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248001637/10000000000 : ℝ), (4440176579/10000000000 : ℝ), (4440177159/10000000000 : ℝ)] ![(8009802782049/25000000000000 : ℝ), (2123774467367/6250000000000 : ℝ), (6796079475801/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248001637/10000000000 : ℝ)|^1033 ≤ (8009802782049/25000000000000 : ℝ)^777
        have hw : |(4248001637/10000000000 : ℝ)|=(4248001637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4440176579/10000000000 : ℝ)|^1033 ≤ (2123774467367/6250000000000 : ℝ)^777
        have hw : |(4440176579/10000000000 : ℝ)|=(4440176579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4440177159/10000000000 : ℝ)|^1033 ≤ (6796079475801/20000000000000 : ℝ)^777
        have hw : |(4440177159/10000000000 : ℝ)|=(4440177159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1071_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14811/25000 : ℝ) ∧ (19897/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20741/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7003/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7003/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7003/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7003/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7003/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7003/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11259/100000 : ℝ) ^ (8263/2048 : ℝ) ≤ (14897613467260009/100000000000000000000 : ℝ) := by
    have hpowers : (11259/100000 : ℝ)^8263 ≤ (14897613467260009/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11259 : ℕ)^8263*100000000000000000000^2048 ≤ 14897613467260009^2048*100000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11259 100000 14897613467260009 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11259/100000 : ℝ)) (X := (14897613467260009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7003/50000 : ℝ) ^ (8263/2048 : ℝ) ≤ (14378743088183/40000000000000000 : ℝ) := by
    have hpowers : (7003/50000 : ℝ)^8263 ≤ (14378743088183/40000000000000000 : ℝ)^2048 := by
      have hnat : (7003 : ℕ)^8263*40000000000000000^2048 ≤ 14378743088183^2048*50000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7003 50000 14378743088183 40000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7003/50000 : ℝ)) (X := (14378743088183/40000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014897613467260009/50000000000000000000 : ℝ) ≤ (10000738397536743/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50014897613467260009/50000000000000000000 : ℝ)^2048 ≤ (10000738397536743/10000000000000000 : ℝ)^8263 := by
      have hnat : (50014897613467260009 : ℕ)^2048*10000000000000000^8263 ≤ 10000738397536743^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014897613467260009 50000000000000000000 10000738397536743 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000738397536743/10000000000000000 : ℝ)) (X := (50014897613467260009/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050844471187717509/100000000000000000000 : ℝ) ≤ (2500314987208057/2500000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (100050844471187717509/100000000000000000000 : ℝ)^2048 ≤ (2500314987208057/2500000000000000 : ℝ)^8263 := by
      have hnat : (100050844471187717509 : ℕ)^2048*2500000000000000^8263 ≤ 2500314987208057^8263*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050844471187717509 100000000000000000000 2500314987208057 2500000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500314987208057/2500000000000000 : ℝ)) (X := (100050844471187717509/100000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (20014378743088183/20000000000000000 : ℝ) ≤ (10001781500127713/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (20014378743088183/20000000000000000 : ℝ)^2048 ≤ (10001781500127713/10000000000000000 : ℝ)^8263 := by
      have hnat : (20014378743088183 : ℕ)^2048*10000000000000000^8263 ≤ 10001781500127713^8263*20000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20014378743088183 20000000000000000 10001781500127713 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001781500127713/10000000000000000 : ℝ)) (X := (20014378743088183/20000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14897613467260009/100000000000000000000 : ℝ) ≤ ((27460284085961701791/27470000000000000000 : ℝ)+2*(104310259097/54940000000000 : ℝ)*(11259/100000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (27460284085961701791/27470000000000000000 : ℝ)+2*(104310259097/54940000000000 : ℝ)*(11259/100000 : ℝ)=(10000738397536743/10000000000000000 : ℝ) by norm_num, show 1+2*(14897613467260009/100000000000000000000 : ℝ)=(50014897613467260009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14378743088183/40000000000000000 : ℝ)+(14897613467260009/100000000000000000000 : ℝ) ≤ ((27460284085961701791/27470000000000000000 : ℝ)+(104310259097/54940000000000 : ℝ)*((7003/50000 : ℝ)+(11259/100000 : ℝ)))^(8263/2048 : ℝ) := by
    rw [show (27460284085961701791/27470000000000000000 : ℝ)+(104310259097/54940000000000 : ℝ)*((7003/50000 : ℝ)+(11259/100000 : ℝ))=(2500314987208057/2500000000000000 : ℝ) by norm_num, show 1+(14378743088183/40000000000000000 : ℝ)+(14897613467260009/100000000000000000000 : ℝ)=(100050844471187717509/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14378743088183/40000000000000000 : ℝ) ≤ ((27460284085961701791/27470000000000000000 : ℝ)+2*(104310259097/54940000000000 : ℝ)*(7003/50000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (27460284085961701791/27470000000000000000 : ℝ)+2*(104310259097/54940000000000 : ℝ)*(7003/50000 : ℝ)=(10001781500127713/10000000000000000 : ℝ) by norm_num, show 1+2*(14378743088183/40000000000000000 : ℝ)=(20014378743088183/20000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27460284085961701791/27470000000000000000 : ℝ)*(X 1 0+X 2 0)+(104310259097/54940000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (27460284085961701791/27470000000000000000 : ℝ)) (alpha := (104310259097/54940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27460284085961701791/27470000000000000000 : ℝ)*(X 0 1+X 2 1)+(104310259097/54940000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (27460284085961701791/27470000000000000000 : ℝ)) (alpha := (104310259097/54940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27460284085961701791/27470000000000000000 : ℝ)*(X 0 2+X 1 2)+(104310259097/54940000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (27460284085961701791/27470000000000000000 : ℝ)) (alpha := (104310259097/54940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2072015907/10000000000 : ℝ)*X 0 0+(2688650841/5000000000 : ℝ)*X 0 1+(1344325347/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647629557/5000000000 : ℝ)*X 1 0+(-2183093267/10000000000 : ℝ)*X 1 1+(5377301583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647629641/5000000000 : ℝ)*X 2 0+(2688650691/5000000000 : ℝ)*X 2 1+(-34110833/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2241553689/5000000000 : ℝ)*X 0 0+(432276723/1000000000 : ℝ)*X 0 1+(4322767237/10000000000 : ℝ)*X 0 2+(2241553689/5000000000 : ℝ)*X 1 0+(432276723/1000000000 : ℝ)*X 1 1+(4322767237/10000000000 : ℝ)*X 1 2+(2241553689/5000000000 : ℝ)*X 2 0+(432276723/1000000000 : ℝ)*X 2 1+(4322767237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2331987423/10000000000 : ℝ)*X 0 0+(264008193/500000000 : ℝ)*X 0 1+(2640081913/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((107279949/200000000 : ℝ)*X 1 0+(-8884343/40000000 : ℝ)*X 1 1+(2640081903/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363997373/10000000000 : ℝ)*X 2 0+(330010249/625000000 : ℝ)*X 2 1+(-138817851/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4266111431/10000000000 : ℝ)*X 0 0+(4431243817/10000000000 : ℝ)*X 0 1+(886248753/2000000000 : ℝ)*X 0 2+(4266111431/10000000000 : ℝ)*X 1 0+(4431243817/10000000000 : ℝ)*X 1 1+(886248753/2000000000 : ℝ)*X 1 2+(4266111431/10000000000 : ℝ)*X 2 0+(4431243817/10000000000 : ℝ)*X 2 1+(886248753/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-569427441/2500000000 : ℝ)*X 0 0+(325890013/625000000 : ℝ)*X 0 1+(2693451539/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288461429/10000000000 : ℝ)*X 1 0+(-1089633173/5000000000 : ℝ)*X 1 1+(2693451707/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288461387/10000000000 : ℝ)*X 2 0+(5386902421/10000000000 : ℝ)*X 2 1+(-108963387/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2252141667/5000000000 : ℝ)*X 0 0+(4312038001/10000000000 : ℝ)*X 0 1+(53900493/125000000 : ℝ)*X 0 2+(2252141667/5000000000 : ℝ)*X 1 0+(4312038001/10000000000 : ℝ)*X 1 1+(53900493/125000000 : ℝ)*X 1 2+(2252141667/5000000000 : ℝ)*X 2 0+(4312038001/10000000000 : ℝ)*X 2 1+(53900493/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2126658743/10000000000 : ℝ)*X 0 0+(5441893823/10000000000 : ℝ)*X 0 1+(2636079917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684829573/5000000000 : ℝ)*X 1 0+(-278019677/1250000000 : ℝ)*X 1 1+(2636079957/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684829633/5000000000 : ℝ)*X 2 0+(1054431937/2000000000 : ℝ)*X 2 1+(-55603939/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4248001637/10000000000 : ℝ)*X 0 0+(4440176579/10000000000 : ℝ)*X 0 1+(4440177159/10000000000 : ℝ)*X 0 2+(4248001637/10000000000 : ℝ)*X 1 0+(4440176579/10000000000 : ℝ)*X 1 1+(4440177159/10000000000 : ℝ)*X 1 2+(4248001637/10000000000 : ℝ)*X 2 0+(4440176579/10000000000 : ℝ)*X 2 1+(4440177159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-213655967187811266812933546942781/343375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17339181/50000000000000 : ℝ)*(upper1) + (17747717/100000000000000 : ℝ)*(upper4) + (58580661/100000000000000 : ℝ)*(upper5) + (965180040385703/25000000000000 : ℝ)*(major0) + (965180040385703/25000000000000 : ℝ)*(major1) + (965180040385703/25000000000000 : ℝ)*(major2) + (1934829049/50000000000000 : ℝ)*(sp1) + (289134477/12500000000000 : ℝ)*(sp3) + (5135171480621973/100000000000000 : ℝ)*(sp4) + (2567586709615413/50000000000000 : ℝ)*(sp5) + (2567561542911561/50000000000000 : ℝ)*(sp6) + (651750375455267/25000000000000 : ℝ)*(sp7) + (5808266951/100000000000000 : ℝ)*(sp8) + (27101532901/50000000000000 : ℝ)*(sp14) + (651750953724221/25000000000000 : ℝ)*(f.failure) + (1283794322222231/25000000000000 : ℝ)*(f.sum) + (16186927744147/2747000000000000000000000000 : ℝ)*base66 + (8786684869394073/686750000000000000000000000000000 : ℝ)*base67 + (8929056798532605927/686750000000000000000000000000000 : ℝ)*base70 + (3299349738027605927/686750000000000000000000000000000 : ℝ)*base72 + (5407015182487/1373500000000000000000000000 : ℝ)*base73 + (1955748548897105927/686750000000000000000000000000000 : ℝ)*base76 + (651159991428105927/686750000000000000000000000000000 : ℝ)*base78 + (1638328490866894073/686750000000000000000000000000000 : ℝ)*base79 + (15074748989/10730468750000000000000000 : ℝ)*base81 + (2203923/500000000000000000000 : ℝ)*base89 + (2203923/500000000000000000000 : ℝ)*base91 + (2203923/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14811/25000 : ℝ) ≤ (50859786516908108400467485124511/85843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2541259/20000000000000 : ℝ)*(upper0) + (179937/25000000000000 : ℝ)*(lower1) + (23898397/100000000000000 : ℝ)*(upper4) + (490465272043443/12500000000000 : ℝ)*(major0) + (490465272043443/12500000000000 : ℝ)*(major1) + (490465272043443/12500000000000 : ℝ)*(major2) + (5178139689992493/100000000000000 : ℝ)*(sp0) + (1294534788179111/25000000000000 : ℝ)*(sp1) + (5178148331654541/100000000000000 : ℝ)*(sp2) + (1324769646095409/50000000000000 : ℝ)*(sp3) + (9440746587/100000000000000 : ℝ)*(sp5) + (261808489/100000000000000 : ℝ)*(sp6) + (7490357077/100000000000000 : ℝ)*(sp7) + (4451735269/50000000000000 : ℝ)*(sp8) + (331193347818487/12500000000000 : ℝ)*(f.failure) + (517814859346303/10000000000000 : ℝ)*(f.sum) + (117043204231/85843750000000000000000000 : ℝ)*base65 + (151390738634281413/343375000000000000000000000000000 : ℝ)*base67 + (871688874449281413/343375000000000000000000000000000 : ℝ)*base69 + (860400373938531413/343375000000000000000000000000000 : ℝ)*base71 + (78133721374729/2747000000000000000000000000 : ℝ)*base74 + (2583837411659031413/343375000000000000000000000000000 : ℝ)*base75 + (3209111060792156413/343375000000000000000000000000000 : ℝ)*base77 + (133566115725218587/343375000000000000000000000000000 : ℝ)*base80 + (11050211673783/2747000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (530681/250000000000000000000 : ℝ)*base89 + (530681/250000000000000000000 : ℝ)*base91 + (530681/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (19897/25000 : ℝ) ≤ (68323387736561984210627921421111/85843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191100841/25000000000000 : ℝ)*(upper0) + (301120991/100000000000000 : ℝ)*(upper2) + (166967083/100000000000000 : ℝ)*(lower3) + (115614723/10000000000000 : ℝ)*(lower5) + (548984231533257/12500000000000 : ℝ)*(major0) + (548984231533257/12500000000000 : ℝ)*(major1) + (548984231533257/12500000000000 : ℝ)*(major2) + (25449518973/6250000000000 : ℝ)*(sp1) + (34873090631/20000000000000 : ℝ)*(sp3) + (688972707/25000000000000 : ℝ)*(sp4) + (46332337942837/800000000000 : ℝ)*(sp8) + (1158227561288377/20000000000000 : ℝ)*(sp9) + (5791544998745453/100000000000000 : ℝ)*(sp10) + (2965498205549247/100000000000000 : ℝ)*(sp11) + (1482836285501201/50000000000000 : ℝ)*(f.failure) + (5791544998745453/100000000000000 : ℝ)*(f.sum) + (148876723399/42921875000000000000000000 : ℝ)*base66 + (2814074658295088287/343375000000000000000000000000000 : ℝ)*base67 + (3603749722536411713/343375000000000000000000000000000 : ℝ)*base70 + (344328261131911713/343375000000000000000000000000000 : ℝ)*base72 + (1734202423091/109880000000000000000000000 : ℝ)*base73 + (785403215590411713/343375000000000000000000000000000 : ℝ)*base76 + (2395324611859161713/343375000000000000000000000000000 : ℝ)*base78 + (5510572739186286713/343375000000000000000000000000000 : ℝ)*base80 + (5143584730233/2747000000000000000000000000 : ℝ)*base82 + (2206337/1000000000000000000000 : ℝ)*base90 + (2206337/1000000000000000000000 : ℝ)*base92 + (2206337/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-20741/25000 : ℝ) ≤ (-569737833278887583641469877357477/686750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38948709/100000000000000 : ℝ)*(lower0) + (189805217/100000000000000 : ℝ)*(lower1) + (520973/781250000000 : ℝ)*(lower2) + (110856769/100000000000000 : ℝ)*(lower4) + (2213247413915449/50000000000000 : ℝ)*(major0) + (2213247413915449/50000000000000 : ℝ)*(major1) + (2213247413915449/50000000000000 : ℝ)*(major2) + (1276712003/12500000000000 : ℝ)*(sp0) + (312424085481/100000000000000 : ℝ)*(sp5) + (128824562247/25000000000000 : ℝ)*(sp6) + (2945791203257493/50000000000000 : ℝ)*(sp12) + (589128019612553/10000000000000 : ℝ)*(sp13) + (5891077321962023/100000000000000 : ℝ)*(sp14) + (1494525427888683/50000000000000 : ℝ)*(sp15) + (1494525427888683/50000000000000 : ℝ)*(f.failure) + (5891592620211011/100000000000000 : ℝ)*(f.sum) + (87558988605217/1373500000000000000000000000 : ℝ)*base65 + (8875169447457630841/1373500000000000000000000000000000 : ℝ)*base68 + (66752229397369159/1373500000000000000000000000000000 : ℝ)*base69 + (74152611332360369159/1373500000000000000000000000000000 : ℝ)*base71 + (3560380776079/1373500000000000000000000000 : ℝ)*base73 + (15358684914647630841/1373500000000000000000000000000000 : ℝ)*base76 + (59539473980078369159/1373500000000000000000000000000000 : ℝ)*base77 + (3621692959318869159/1373500000000000000000000000000000 : ℝ)*base79 + (216736696431/686750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (9918971/1000000000000000000000 : ℝ)*base90 + (9918971/1000000000000000000000 : ℝ)*base92 + (9918971/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1071_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(14811/25000 : ℝ) else (19897/25000 : ℝ) ≤ X j i ∧ X j i ≤ (20741/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1071_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1071_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(14811/25000 : ℝ) else (19897/25000 : ℝ) ≤ X j i ∧ X j i ≤ (20741/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1071_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1071_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(14811/25000 : ℝ) else (19897/25000 : ℝ) ≤ X j i ∧ X j i ≤ (20741/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1071_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
