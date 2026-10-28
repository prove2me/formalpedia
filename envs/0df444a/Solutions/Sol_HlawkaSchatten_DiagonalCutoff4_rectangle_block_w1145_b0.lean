-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1145_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:33:28.025859+00:00
-- url     : https://prove2.me/submissions/7f33482b-c332-411a-8e2a-a79d3f403023

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
theorem support_rectangle_w1145_s0_0 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-37817233/200000000 : ℝ)*x 0 + (3026818537/5000000000 : ℝ)*x 1 + (2390425779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37817233/200000000 : ℝ)^4169 ≤ (10993675896869/100000000000000 : ℝ)^3145 := by
    have hnat : (37817233 : ℕ)^4169*100000000000000^3145 ≤ 10993675896869^3145*200000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37817233 200000000 10993675896869 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3026818537/5000000000 : ℝ)^4169 ≤ (51409306572667/100000000000000 : ℝ)^3145 := by
    have hnat : (3026818537 : ℕ)^4169*100000000000000^3145 ≤ 51409306572667^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3026818537 5000000000 51409306572667 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2390425779/5000000000 : ℝ)^4169 ≤ (3759701751403/10000000000000 : ℝ)^3145 := by
    have hnat : (2390425779 : ℕ)^4169*10000000000000^3145 ≤ 3759701751403^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390425779 5000000000 3759701751403 10000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37817233/200000000 : ℝ), (3026818537/5000000000 : ℝ), (2390425779/5000000000 : ℝ)] ![(10993675896869/100000000000000 : ℝ), (51409306572667/100000000000000 : ℝ), (3759701751403/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37817233/200000000 : ℝ)|^4169 ≤ (10993675896869/100000000000000 : ℝ)^3145
        have hw : |(-37817233/200000000 : ℝ)|=(37817233/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3026818537/5000000000 : ℝ)|^4169 ≤ (51409306572667/100000000000000 : ℝ)^3145
        have hw : |(3026818537/5000000000 : ℝ)|=(3026818537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2390425779/5000000000 : ℝ)|^4169 ≤ (3759701751403/10000000000000 : ℝ)^3145
        have hw : |(2390425779/5000000000 : ℝ)|=(2390425779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s0_1 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5516624589/10000000000 : ℝ)*x 0 + (-2621205679/10000000000 : ℝ)*x 1 + (4780851601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516624589/10000000000 : ℝ)^4169 ≤ (45453076683119/100000000000000 : ℝ)^3145 := by
    have hnat : (5516624589 : ℕ)^4169*100000000000000^3145 ≤ 45453076683119^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516624589 10000000000 45453076683119 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621205679/10000000000 : ℝ)^4169 ≤ (16949905341933/100000000000000 : ℝ)^3145 := by
    have hnat : (2621205679 : ℕ)^4169*100000000000000^3145 ≤ 16949905341933^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621205679 10000000000 16949905341933 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4780851601/10000000000 : ℝ)^4169 ≤ (2349813622643/6250000000000 : ℝ)^3145 := by
    have hnat : (4780851601 : ℕ)^4169*6250000000000^3145 ≤ 2349813622643^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4780851601 10000000000 2349813622643 6250000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516624589/10000000000 : ℝ), (-2621205679/10000000000 : ℝ), (4780851601/10000000000 : ℝ)] ![(45453076683119/100000000000000 : ℝ), (16949905341933/100000000000000 : ℝ), (2349813622643/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516624589/10000000000 : ℝ)|^4169 ≤ (45453076683119/100000000000000 : ℝ)^3145
        have hw : |(5516624589/10000000000 : ℝ)|=(5516624589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2621205679/10000000000 : ℝ)|^4169 ≤ (16949905341933/100000000000000 : ℝ)^3145
        have hw : |(-2621205679/10000000000 : ℝ)|=(2621205679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4780851601/10000000000 : ℝ)|^4169 ≤ (2349813622643/6250000000000 : ℝ)^3145
        have hw : |(4780851601/10000000000 : ℝ)|=(4780851601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s0_2 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5516624793/10000000000 : ℝ)*x 0 + (4780851513/10000000000 : ℝ)*x 1 + (-2621205527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516624793/10000000000 : ℝ)^4169 ≤ (45453078911201/100000000000000 : ℝ)^3145 := by
    have hnat : (5516624793 : ℕ)^4169*100000000000000^3145 ≤ 45453078911201^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516624793 10000000000 45453078911201 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4780851513/10000000000 : ℝ)^4169 ≤ (37597017044923/100000000000000 : ℝ)^3145 := by
    have hnat : (4780851513 : ℕ)^4169*100000000000000^3145 ≤ 37597017044923^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4780851513 10000000000 37597017044923 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621205527/10000000000 : ℝ)^4169 ≤ (16949904039003/100000000000000 : ℝ)^3145 := by
    have hnat : (2621205527 : ℕ)^4169*100000000000000^3145 ≤ 16949904039003^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621205527 10000000000 16949904039003 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516624793/10000000000 : ℝ), (4780851513/10000000000 : ℝ), (-2621205527/10000000000 : ℝ)] ![(45453078911201/100000000000000 : ℝ), (37597017044923/100000000000000 : ℝ), (16949904039003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516624793/10000000000 : ℝ)|^4169 ≤ (45453078911201/100000000000000 : ℝ)^3145
        have hw : |(5516624793/10000000000 : ℝ)|=(5516624793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4780851513/10000000000 : ℝ)|^4169 ≤ (37597017044923/100000000000000 : ℝ)^3145
        have hw : |(4780851513/10000000000 : ℝ)|=(4780851513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2621205527/10000000000 : ℝ)|^4169 ≤ (16949904039003/100000000000000 : ℝ)^3145
        have hw : |(-2621205527/10000000000 : ℝ)|=(2621205527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s0_3 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4200748311/10000000000 : ℝ)*x 0 + (12191171/39062500 : ℝ)*x 1 + (706825479/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200748311/10000000000 : ℝ)^4169 ≤ (31672566716623/100000000000000 : ℝ)^3145 := by
    have hnat : (4200748311 : ℕ)^4169*100000000000000^3145 ≤ 31672566716623^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200748311 10000000000 31672566716623 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12191171/39062500 : ℝ)^4169 ≤ (4272249778699/20000000000000 : ℝ)^3145 := by
    have hnat : (12191171 : ℕ)^4169*20000000000000^3145 ≤ 4272249778699^3145*39062500^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12191171 39062500 4272249778699 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706825479/1250000000 : ℝ)^4169 ≤ (2935386523749/6250000000000 : ℝ)^3145 := by
    have hnat : (706825479 : ℕ)^4169*6250000000000^3145 ≤ 2935386523749^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706825479 1250000000 2935386523749 6250000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200748311/10000000000 : ℝ), (12191171/39062500 : ℝ), (706825479/1250000000 : ℝ)] ![(31672566716623/100000000000000 : ℝ), (4272249778699/20000000000000 : ℝ), (2935386523749/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200748311/10000000000 : ℝ)|^4169 ≤ (31672566716623/100000000000000 : ℝ)^3145
        have hw : |(4200748311/10000000000 : ℝ)|=(4200748311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12191171/39062500 : ℝ)|^4169 ≤ (4272249778699/20000000000000 : ℝ)^3145
        have hw : |(12191171/39062500 : ℝ)|=(12191171/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(706825479/1250000000 : ℝ)|^4169 ≤ (2935386523749/6250000000000 : ℝ)^3145
        have hw : |(706825479/1250000000 : ℝ)|=(706825479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s0_4 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1895998359/10000000000 : ℝ)*x 0 + (4813684361/10000000000 : ℝ)*x 1 + (3009824857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1895998359/10000000000 : ℝ)^4169 ≤ (2758320709307/25000000000000 : ℝ)^3145 := by
    have hnat : (1895998359 : ℕ)^4169*25000000000000^3145 ≤ 2758320709307^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895998359 10000000000 2758320709307 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4813684361/10000000000 : ℝ)^4169 ≤ (18969834206803/50000000000000 : ℝ)^3145 := by
    have hnat : (4813684361 : ℕ)^4169*50000000000000^3145 ≤ 18969834206803^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4813684361 10000000000 18969834206803 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3009824857/5000000000 : ℝ)^4169 ≤ (1020540974517/2000000000000 : ℝ)^3145 := by
    have hnat : (3009824857 : ℕ)^4169*2000000000000^3145 ≤ 1020540974517^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3009824857 5000000000 1020540974517 2000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1895998359/10000000000 : ℝ), (4813684361/10000000000 : ℝ), (3009824857/5000000000 : ℝ)] ![(2758320709307/25000000000000 : ℝ), (18969834206803/50000000000000 : ℝ), (1020540974517/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1895998359/10000000000 : ℝ)|^4169 ≤ (2758320709307/25000000000000 : ℝ)^3145
        have hw : |(-1895998359/10000000000 : ℝ)|=(1895998359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4813684361/10000000000 : ℝ)|^4169 ≤ (18969834206803/50000000000000 : ℝ)^3145
        have hw : |(4813684361/10000000000 : ℝ)|=(4813684361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3009824857/5000000000 : ℝ)|^4169 ≤ (1020540974517/2000000000000 : ℝ)^3145
        have hw : |(3009824857/5000000000 : ℝ)|=(3009824857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s0_5 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5170765579/10000000000 : ℝ)*x 0 + (-1382407591/10000000000 : ℝ)*x 1 + (6019649571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170765579/10000000000 : ℝ)^4169 ≤ (2085736327087/5000000000000 : ℝ)^3145 := by
    have hnat : (5170765579 : ℕ)^4169*5000000000000^3145 ≤ 2085736327087^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170765579 10000000000 2085736327087 5000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382407591/10000000000 : ℝ)^4169 ≤ (7258226326503/100000000000000 : ℝ)^3145 := by
    have hnat : (1382407591 : ℕ)^4169*100000000000000^3145 ≤ 7258226326503^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382407591 10000000000 7258226326503 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6019649571/10000000000 : ℝ)^4169 ≤ (12756761779749/25000000000000 : ℝ)^3145 := by
    have hnat : (6019649571 : ℕ)^4169*25000000000000^3145 ≤ 12756761779749^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6019649571 10000000000 12756761779749 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170765579/10000000000 : ℝ), (-1382407591/10000000000 : ℝ), (6019649571/10000000000 : ℝ)] ![(2085736327087/5000000000000 : ℝ), (7258226326503/100000000000000 : ℝ), (12756761779749/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170765579/10000000000 : ℝ)|^4169 ≤ (2085736327087/5000000000000 : ℝ)^3145
        have hw : |(5170765579/10000000000 : ℝ)|=(5170765579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1382407591/10000000000 : ℝ)|^4169 ≤ (7258226326503/100000000000000 : ℝ)^3145
        have hw : |(-1382407591/10000000000 : ℝ)|=(1382407591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6019649571/10000000000 : ℝ)|^4169 ≤ (12756761779749/25000000000000 : ℝ)^3145
        have hw : |(6019649571/10000000000 : ℝ)|=(6019649571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s0_6 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2585382789/5000000000 : ℝ)*x 0 + (3009824801/5000000000 : ℝ)*x 1 + (-691203771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585382789/5000000000 : ℝ)^4169 ≤ (8342945306209/20000000000000 : ℝ)^3145 := by
    have hnat : (2585382789 : ℕ)^4169*20000000000000^3145 ≤ 8342945306209^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585382789 5000000000 8342945306209 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3009824801/5000000000 : ℝ)^4169 ≤ (10205409493467/20000000000000 : ℝ)^3145 := by
    have hnat : (3009824801 : ℕ)^4169*20000000000000^3145 ≤ 10205409493467^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3009824801 5000000000 10205409493467 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691203771/5000000000 : ℝ)^4169 ≤ (3629112992733/50000000000000 : ℝ)^3145 := by
    have hnat : (691203771 : ℕ)^4169*50000000000000^3145 ≤ 3629112992733^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691203771 5000000000 3629112992733 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585382789/5000000000 : ℝ), (3009824801/5000000000 : ℝ), (-691203771/5000000000 : ℝ)] ![(8342945306209/20000000000000 : ℝ), (10205409493467/20000000000000 : ℝ), (3629112992733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585382789/5000000000 : ℝ)|^4169 ≤ (8342945306209/20000000000000 : ℝ)^3145
        have hw : |(2585382789/5000000000 : ℝ)|=(2585382789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3009824801/5000000000 : ℝ)|^4169 ≤ (10205409493467/20000000000000 : ℝ)^3145
        have hw : |(3009824801/5000000000 : ℝ)|=(3009824801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-691203771/5000000000 : ℝ)|^4169 ≤ (3629112992733/50000000000000 : ℝ)^3145
        have hw : |(-691203771/5000000000 : ℝ)|=(691203771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s0_7 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052743479/2500000000 : ℝ)*x 0 + (2794622601/5000000000 : ℝ)*x 1 + (797149207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052743479/2500000000 : ℝ)^4169 ≤ (15887404299177/50000000000000 : ℝ)^3145 := by
    have hnat : (1052743479 : ℕ)^4169*50000000000000^3145 ≤ 15887404299177^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052743479 2500000000 15887404299177 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794622601/5000000000 : ℝ)^4169 ≤ (46247931853657/100000000000000 : ℝ)^3145 := by
    have hnat : (2794622601 : ℕ)^4169*100000000000000^3145 ≤ 46247931853657^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794622601 5000000000 46247931853657 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (797149207/2500000000 : ℝ)^4169 ≤ (21977259525251/100000000000000 : ℝ)^3145 := by
    have hnat : (797149207 : ℕ)^4169*100000000000000^3145 ≤ 21977259525251^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797149207 2500000000 21977259525251 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052743479/2500000000 : ℝ), (2794622601/5000000000 : ℝ), (797149207/2500000000 : ℝ)] ![(15887404299177/50000000000000 : ℝ), (46247931853657/100000000000000 : ℝ), (21977259525251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052743479/2500000000 : ℝ)|^4169 ≤ (15887404299177/50000000000000 : ℝ)^3145
        have hw : |(1052743479/2500000000 : ℝ)|=(1052743479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2794622601/5000000000 : ℝ)|^4169 ≤ (46247931853657/100000000000000 : ℝ)^3145
        have hw : |(2794622601/5000000000 : ℝ)|=(2794622601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(797149207/2500000000 : ℝ)|^4169 ≤ (21977259525251/100000000000000 : ℝ)^3145
        have hw : |(797149207/2500000000 : ℝ)|=(797149207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1145_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (213/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6951/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8337/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8337 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8337*1^2048 ≤ 0^2048*1^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8337/2048 : ℝ) ≤ (1199597373322708979/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8337 ≤ (1199597373322708979/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8337*50000000000000000000^2048 ≤ 1199597373322708979^2048*5^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1199597373322708979 50000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1199597373322708979/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8337 := by
      have hnat : (1 : ℕ)^2048*1^8337 ≤ 1^8337*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51199597373322708979/50000000000000000000 : ℝ) ≤ (2011682142578241/2000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (51199597373322708979/50000000000000000000 : ℝ)^2048 ≤ (2011682142578241/2000000000000000 : ℝ)^8337 := by
      have hnat : (51199597373322708979 : ℕ)^2048*2000000000000000^8337 ≤ 2011682142578241^8337*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51199597373322708979 50000000000000000000 2011682142578241 2000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011682142578241/2000000000000000 : ℝ)) (X := (51199597373322708979/50000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26199597373322708979/25000000000000000000 : ℝ) ≤ (1011682142578241/1000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (26199597373322708979/25000000000000000000 : ℝ)^2048 ≤ (1011682142578241/1000000000000000 : ℝ)^8337 := by
      have hnat : (26199597373322708979 : ℕ)^2048*1000000000000000^8337 ≤ 1011682142578241^8337*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26199597373322708979 25000000000000000000 1011682142578241 1000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011682142578241/1000000000000000 : ℝ)) (X := (26199597373322708979/25000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11682142578241/800000000000000 : ℝ)*(0 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11682142578241/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1199597373322708979/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11682142578241/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8337/2048 : ℝ) := by
    rw [show (1 : ℝ)+(11682142578241/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011682142578241/2000000000000000 : ℝ) by norm_num, show 1+(1199597373322708979/50000000000000000000 : ℝ)+(0 : ℝ)=(51199597373322708979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1199597373322708979/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11682142578241/800000000000000 : ℝ)*(2/5 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11682142578241/800000000000000 : ℝ)*(2/5 : ℝ)=(1011682142578241/1000000000000000 : ℝ) by norm_num, show 1+2*(1199597373322708979/50000000000000000000 : ℝ)=(26199597373322708979/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11682142578241/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11682142578241/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11682142578241/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11682142578241/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11682142578241/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11682142578241/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-37817233/200000000 : ℝ)*X 0 0+(3026818537/5000000000 : ℝ)*X 0 1+(2390425779/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5516624589/10000000000 : ℝ)*X 1 0+(-2621205679/10000000000 : ℝ)*X 1 1+(4780851601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5516624793/10000000000 : ℝ)*X 2 0+(4780851513/10000000000 : ℝ)*X 2 1+(-2621205527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4200748311/10000000000 : ℝ)*X 0 0+(12191171/39062500 : ℝ)*X 0 1+(706825479/1250000000 : ℝ)*X 0 2+(4200748311/10000000000 : ℝ)*X 1 0+(12191171/39062500 : ℝ)*X 1 1+(706825479/1250000000 : ℝ)*X 1 2+(4200748311/10000000000 : ℝ)*X 2 0+(12191171/39062500 : ℝ)*X 2 1+(706825479/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1895998359/10000000000 : ℝ)*X 0 0+(4813684361/10000000000 : ℝ)*X 0 1+(3009824857/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5170765579/10000000000 : ℝ)*X 1 0+(-1382407591/10000000000 : ℝ)*X 1 1+(6019649571/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585382789/5000000000 : ℝ)*X 2 0+(3009824801/5000000000 : ℝ)*X 2 1+(-691203771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052743479/2500000000 : ℝ)*X 0 0+(2794622601/5000000000 : ℝ)*X 0 1+(797149207/2500000000 : ℝ)*X 0 2+(1052743479/2500000000 : ℝ)*X 1 0+(2794622601/5000000000 : ℝ)*X 1 1+(797149207/2500000000 : ℝ)*X 1 2+(1052743479/2500000000 : ℝ)*X 2 0+(2794622601/5000000000 : ℝ)*X 2 1+(797149207/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3431696529341374084713/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33843131/100000000000000 : ℝ)*(base1) + (860471721/100000000000000 : ℝ)*(base19) + (815149657/100000000000000 : ℝ)*(base23) + (7437591/10000000000000 : ℝ)*(base24) + (50393421/25000000000000 : ℝ)*(upper3) + (59018546016869/10000000000000 : ℝ)*(major0) + (59018546016869/10000000000000 : ℝ)*(major1) + (59018546016869/10000000000000 : ℝ)*(major2) + (785681190485169/100000000000000 : ℝ)*(sp0) + (157136438178469/20000000000000 : ℝ)*(sp1) + (785682161838499/100000000000000 : ℝ)*(sp2) + (394686188826399/100000000000000 : ℝ)*(sp3) + (473680507/25000000000000 : ℝ)*(sp4) + (765956949/50000000000000 : ℝ)*(sp7) + (98671938645857/25000000000000 : ℝ)*(f.failure) + (392841525682033/50000000000000 : ℝ)*(f.sum) + (13511435327429/4000000000000000000000000000 : ℝ)*base65 + (6102650724571/8000000000000000000000000000 : ℝ)*base68 + (28873820100571/8000000000000000000000000000 : ℝ)*base70 + (13230995451429/8000000000000000000000000000 : ℝ)*base71 + (9600991287429/4000000000000000000000000000 : ℝ)*base73 + (1024971491429/8000000000000000000000000000 : ℝ)*base75 + (15099519435429/8000000000000000000000000000 : ℝ)*base77 + (1301834291429/8000000000000000000000000000 : ℝ)*base79 + (161168191429/4000000000000000000000000000 : ℝ)*base81 + (1431793/500000000000000000000 : ℝ)*base89 + (1431793/500000000000000000000 : ℝ)*base91 + (1431793/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (334231899102573061355151/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50081649/50000000000000 : ℝ)*(base1) + (258013449/12500000000000 : ℝ)*(base19) + (515846489/25000000000000 : ℝ)*(base23) + (14198951/6250000000000 : ℝ)*(upper3) + (241060397/100000000000000 : ℝ)*(upper5) + (622882839928279/100000000000000 : ℝ)*(major0) + (622882839928279/100000000000000 : ℝ)*(major1) + (622882839928279/100000000000000 : ℝ)*(major2) + (1053947927/25000000000000 : ℝ)*(sp1) + (2103698967/50000000000000 : ℝ)*(sp2) + (41460565307841/5000000000000 : ℝ)*(sp4) + (829204926094221/100000000000000 : ℝ)*(sp5) + (25912654225301/3125000000000 : ℝ)*(sp6) + (13017315474161/3125000000000 : ℝ)*(sp7) + (8331083906729/2000000000000 : ℝ)*(f.failure) + (414605602996761/50000000000000 : ℝ)*(f.sum) + (69017208102761/40000000000000000000000000000 : ℝ)*base66 + (148480111942761/80000000000000000000000000000 : ℝ)*base68 + (18927679097239/80000000000000000000000000000 : ℝ)*base69 + (230278169737239/80000000000000000000000000000 : ℝ)*base71 + (162378428462761/40000000000000000000000000000 : ℝ)*base74 + (589295341577239/80000000000000000000000000000 : ℝ)*base75 + (311185669222761/80000000000000000000000000000 : ℝ)*base78 + (1667998822761/80000000000000000000000000000 : ℝ)*base80 + (61100857782761/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4679/40000000000000000000 : ℝ)*base90 + (4679/40000000000000000000 : ℝ)*base92 + (4679/40000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1145_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (213/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6951/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1145_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1145_s1_0 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-261913021/1250000000 : ℝ)*x 0 + (142517897/250000000 : ℝ)*x 1 + (5002890293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261913021/1250000000 : ℝ)^4169 ≤ (6298218442651/50000000000000 : ℝ)^3145 := by
    have hnat : (261913021 : ℕ)^4169*50000000000000^3145 ≤ 6298218442651^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261913021 1250000000 6298218442651 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142517897/250000000 : ℝ)^4169 ≤ (9494911804391/20000000000000 : ℝ)^3145 := by
    have hnat : (142517897 : ℕ)^4169*20000000000000^3145 ≤ 9494911804391^3145*250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142517897 250000000 9494911804391 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5002890293/10000000000 : ℝ)^4169 ≤ (7985800815721/20000000000000 : ℝ)^3145 := by
    have hnat : (5002890293 : ℕ)^4169*20000000000000^3145 ≤ 7985800815721^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002890293 10000000000 7985800815721 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261913021/1250000000 : ℝ), (142517897/250000000 : ℝ), (5002890293/10000000000 : ℝ)] ![(6298218442651/50000000000000 : ℝ), (9494911804391/20000000000000 : ℝ), (7985800815721/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261913021/1250000000 : ℝ)|^4169 ≤ (6298218442651/50000000000000 : ℝ)^3145
        have hw : |(-261913021/1250000000 : ℝ)|=(261913021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142517897/250000000 : ℝ)|^4169 ≤ (9494911804391/20000000000000 : ℝ)^3145
        have hw : |(142517897/250000000 : ℝ)|=(142517897/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5002890293/10000000000 : ℝ)|^4169 ≤ (7985800815721/20000000000000 : ℝ)^3145
        have hw : |(5002890293/10000000000 : ℝ)|=(5002890293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s1_1 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2709480231/5000000000 : ℝ)*x 0 + (-617958077/2500000000 : ℝ)*x 1 + (5002889543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709480231/5000000000 : ℝ)^4169 ≤ (11097369588531/25000000000000 : ℝ)^3145 := by
    have hnat : (2709480231 : ℕ)^4169*25000000000000^3145 ≤ 11097369588531^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709480231 5000000000 11097369588531 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (617958077/2500000000 : ℝ)^4169 ≤ (15681525484589/100000000000000 : ℝ)^3145 := by
    have hnat : (617958077 : ℕ)^4169*100000000000000^3145 ≤ 15681525484589^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617958077 2500000000 15681525484589 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5002889543/10000000000 : ℝ)^4169 ≤ (9982249035933/25000000000000 : ℝ)^3145 := by
    have hnat : (5002889543 : ℕ)^4169*25000000000000^3145 ≤ 9982249035933^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002889543 10000000000 9982249035933 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709480231/5000000000 : ℝ), (-617958077/2500000000 : ℝ), (5002889543/10000000000 : ℝ)] ![(11097369588531/25000000000000 : ℝ), (15681525484589/100000000000000 : ℝ), (9982249035933/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709480231/5000000000 : ℝ)|^4169 ≤ (11097369588531/25000000000000 : ℝ)^3145
        have hw : |(2709480231/5000000000 : ℝ)|=(2709480231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-617958077/2500000000 : ℝ)|^4169 ≤ (15681525484589/100000000000000 : ℝ)^3145
        have hw : |(-617958077/2500000000 : ℝ)|=(617958077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5002889543/10000000000 : ℝ)|^4169 ≤ (9982249035933/25000000000000 : ℝ)^3145
        have hw : |(5002889543/10000000000 : ℝ)|=(5002889543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s1_2 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5418962441/10000000000 : ℝ)*x 0 + (5002887783/10000000000 : ℝ)*x 1 + (-1235915983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5418962441/10000000000 : ℝ)^4169 ≤ (44389499843367/100000000000000 : ℝ)^3145 := by
    have hnat : (5418962441 : ℕ)^4169*100000000000000^3145 ≤ 44389499843367^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418962441 10000000000 44389499843367 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5002887783/10000000000 : ℝ)^4169 ≤ (39928977523231/100000000000000 : ℝ)^3145 := by
    have hnat : (5002887783 : ℕ)^4169*100000000000000^3145 ≤ 39928977523231^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002887783 10000000000 39928977523231 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1235915983/5000000000 : ℝ)^4169 ≤ (15681522608471/100000000000000 : ℝ)^3145 := by
    have hnat : (1235915983 : ℕ)^4169*100000000000000^3145 ≤ 15681522608471^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235915983 5000000000 15681522608471 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5418962441/10000000000 : ℝ), (5002887783/10000000000 : ℝ), (-1235915983/5000000000 : ℝ)] ![(44389499843367/100000000000000 : ℝ), (39928977523231/100000000000000 : ℝ), (15681522608471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5418962441/10000000000 : ℝ)|^4169 ≤ (44389499843367/100000000000000 : ℝ)^3145
        have hw : |(5418962441/10000000000 : ℝ)|=(5418962441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5002887783/10000000000 : ℝ)|^4169 ≤ (39928977523231/100000000000000 : ℝ)^3145
        have hw : |(5002887783/10000000000 : ℝ)|=(5002887783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1235915983/5000000000 : ℝ)|^4169 ≤ (15681522608471/100000000000000 : ℝ)^3145
        have hw : |(-1235915983/5000000000 : ℝ)|=(1235915983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s1_3 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4317182589/10000000000 : ℝ)*x 0 + (1838794109/5000000000 : ℝ)*x 1 + (633338529/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317182589/10000000000 : ℝ)^4169 ≤ (8210376507427/25000000000000 : ℝ)^3145 := by
    have hnat : (4317182589 : ℕ)^4169*25000000000000^3145 ≤ 8210376507427^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317182589 10000000000 8210376507427 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1838794109/5000000000 : ℝ)^4169 ≤ (265529086991/1000000000000 : ℝ)^3145 := by
    have hnat : (1838794109 : ℕ)^4169*1000000000000^3145 ≤ 265529086991^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838794109 5000000000 265529086991 1000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (633338529/1250000000 : ℝ)^4169 ≤ (40605585253489/100000000000000 : ℝ)^3145 := by
    have hnat : (633338529 : ℕ)^4169*100000000000000^3145 ≤ 40605585253489^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633338529 1250000000 40605585253489 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317182589/10000000000 : ℝ), (1838794109/5000000000 : ℝ), (633338529/1250000000 : ℝ)] ![(8210376507427/25000000000000 : ℝ), (265529086991/1000000000000 : ℝ), (40605585253489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317182589/10000000000 : ℝ)|^4169 ≤ (8210376507427/25000000000000 : ℝ)^3145
        have hw : |(4317182589/10000000000 : ℝ)|=(4317182589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1838794109/5000000000 : ℝ)|^4169 ≤ (265529086991/1000000000000 : ℝ)^3145
        have hw : |(1838794109/5000000000 : ℝ)|=(1838794109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(633338529/1250000000 : ℝ)|^4169 ≤ (40605585253489/100000000000000 : ℝ)^3145
        have hw : |(633338529/1250000000 : ℝ)|=(633338529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s1_4 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096110821/10000000000 : ℝ)*x 0 + (1002481573/2000000000 : ℝ)*x 1 + (5691006601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096110821/10000000000 : ℝ)^4169 ≤ (6301432812583/50000000000000 : ℝ)^3145 := by
    have hnat : (2096110821 : ℕ)^4169*50000000000000^3145 ≤ 6301432812583^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096110821 10000000000 6301432812583 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002481573/2000000000 : ℝ)^4169 ≤ (10007432389419/25000000000000 : ℝ)^3145 := by
    have hnat : (1002481573 : ℕ)^4169*25000000000000^3145 ≤ 10007432389419^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002481573 2000000000 10007432389419 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5691006601/10000000000 : ℝ)^4169 ≤ (47367404799751/100000000000000 : ℝ)^3145 := by
    have hnat : (5691006601 : ℕ)^4169*100000000000000^3145 ≤ 47367404799751^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5691006601 10000000000 47367404799751 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096110821/10000000000 : ℝ), (1002481573/2000000000 : ℝ), (5691006601/10000000000 : ℝ)] ![(6301432812583/50000000000000 : ℝ), (10007432389419/25000000000000 : ℝ), (47367404799751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096110821/10000000000 : ℝ)|^4169 ≤ (6301432812583/50000000000000 : ℝ)^3145
        have hw : |(-2096110821/10000000000 : ℝ)|=(2096110821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1002481573/2000000000 : ℝ)|^4169 ≤ (10007432389419/25000000000000 : ℝ)^3145
        have hw : |(1002481573/2000000000 : ℝ)|=(1002481573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5691006601/10000000000 : ℝ)|^4169 ≤ (47367404799751/100000000000000 : ℝ)^3145
        have hw : |(5691006601/10000000000 : ℝ)|=(5691006601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s1_5 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5240023219/10000000000 : ℝ)*x 0 + (-35674221/200000000 : ℝ)*x 1 + (569101029/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5240023219/10000000000 : ℝ)^4169 ≤ (42456987499653/100000000000000 : ℝ)^3145 := by
    have hnat : (5240023219 : ℕ)^4169*100000000000000^3145 ≤ 42456987499653^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240023219 10000000000 42456987499653 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35674221/200000000 : ℝ)^4169 ≤ (2035113396637/20000000000000 : ℝ)^3145 := by
    have hnat : (35674221 : ℕ)^4169*20000000000000^3145 ≤ 2035113396637^3145*200000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35674221 200000000 2035113396637 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569101029/1000000000 : ℝ)^4169 ≤ (23683722750627/50000000000000 : ℝ)^3145 := by
    have hnat : (569101029 : ℕ)^4169*50000000000000^3145 ≤ 23683722750627^3145*1000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569101029 1000000000 23683722750627 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5240023219/10000000000 : ℝ), (-35674221/200000000 : ℝ), (569101029/1000000000 : ℝ)] ![(42456987499653/100000000000000 : ℝ), (2035113396637/20000000000000 : ℝ), (23683722750627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5240023219/10000000000 : ℝ)|^4169 ≤ (42456987499653/100000000000000 : ℝ)^3145
        have hw : |(5240023219/10000000000 : ℝ)|=(5240023219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35674221/200000000 : ℝ)|^4169 ≤ (2035113396637/20000000000000 : ℝ)^3145
        have hw : |(-35674221/200000000 : ℝ)|=(35674221/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(569101029/1000000000 : ℝ)|^4169 ≤ (23683722750627/50000000000000 : ℝ)^3145
        have hw : |(569101029/1000000000 : ℝ)|=(569101029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s1_6 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2620010897/5000000000 : ℝ)*x 0 + (5691012163/10000000000 : ℝ)*x 1 + (-1783710341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620010897/5000000000 : ℝ)^4169 ≤ (21228486097173/50000000000000 : ℝ)^3145 := by
    have hnat : (2620010897 : ℕ)^4169*50000000000000^3145 ≤ 21228486097173^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620010897 5000000000 21228486097173 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5691012163/10000000000 : ℝ)^4169 ≤ (9473493233291/20000000000000 : ℝ)^3145 := by
    have hnat : (5691012163 : ℕ)^4169*20000000000000^3145 ≤ 9473493233291^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5691012163 10000000000 9473493233291 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1783710341/10000000000 : ℝ)^4169 ≤ (508778081081/5000000000000 : ℝ)^3145 := by
    have hnat : (1783710341 : ℕ)^4169*5000000000000^3145 ≤ 508778081081^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783710341 10000000000 508778081081 5000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620010897/5000000000 : ℝ), (5691012163/10000000000 : ℝ), (-1783710341/10000000000 : ℝ)] ![(21228486097173/50000000000000 : ℝ), (9473493233291/20000000000000 : ℝ), (508778081081/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620010897/5000000000 : ℝ)|^4169 ≤ (21228486097173/50000000000000 : ℝ)^3145
        have hw : |(2620010897/5000000000 : ℝ)|=(2620010897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5691012163/10000000000 : ℝ)|^4169 ≤ (9473493233291/20000000000000 : ℝ)^3145
        have hw : |(5691012163/10000000000 : ℝ)|=(5691012163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1783710341/10000000000 : ℝ)|^4169 ≤ (508778081081/5000000000000 : ℝ)^3145
        have hw : |(-1783710341/10000000000 : ℝ)|=(1783710341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s1_7 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318777801/10000000000 : ℝ)*x 0 + (5047762257/10000000000 : ℝ)*x 1 + (3696907541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318777801/10000000000 : ℝ)^4169 ≤ (32857593154203/100000000000000 : ℝ)^3145 := by
    have hnat : (4318777801 : ℕ)^4169*100000000000000^3145 ≤ 32857593154203^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318777801 10000000000 32857593154203 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5047762257/10000000000 : ℝ)^4169 ≤ (10101108423631/25000000000000 : ℝ)^3145 := by
    have hnat : (5047762257 : ℕ)^4169*25000000000000^3145 ≤ 10101108423631^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5047762257 10000000000 10101108423631 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3696907541/10000000000 : ℝ)^4169 ≤ (2673797313731/10000000000000 : ℝ)^3145 := by
    have hnat : (3696907541 : ℕ)^4169*10000000000000^3145 ≤ 2673797313731^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3696907541 10000000000 2673797313731 10000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318777801/10000000000 : ℝ), (5047762257/10000000000 : ℝ), (3696907541/10000000000 : ℝ)] ![(32857593154203/100000000000000 : ℝ), (10101108423631/25000000000000 : ℝ), (2673797313731/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318777801/10000000000 : ℝ)|^4169 ≤ (32857593154203/100000000000000 : ℝ)^3145
        have hw : |(4318777801/10000000000 : ℝ)|=(4318777801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5047762257/10000000000 : ℝ)|^4169 ≤ (10101108423631/25000000000000 : ℝ)^3145
        have hw : |(5047762257/10000000000 : ℝ)|=(5047762257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3696907541/10000000000 : ℝ)|^4169 ≤ (2673797313731/10000000000000 : ℝ)^3145
        have hw : |(3696907541/10000000000 : ℝ)|=(3696907541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1145_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6951/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2833/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2553/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6951/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (213/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6951/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (213/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6951/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (213/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6951/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (213/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6951/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (213/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6951/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (213/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (213/50000 : ℝ) ^ (8337/2048 : ℝ) ≤ (22376839353/100000000000000000000 : ℝ) := by
    have hpowers : (213/50000 : ℝ)^8337 ≤ (22376839353/100000000000000000000 : ℝ)^2048 := by
      have hnat : (213 : ℕ)^8337*100000000000000000000^2048 ≤ 22376839353^2048*50000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        213 50000 22376839353 100000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (213/50000 : ℝ)) (X := (22376839353/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6951/25000 : ℝ) ^ (8337/2048 : ℝ) ≤ (54584769469857079/10000000000000000000 : ℝ) := by
    have hpowers : (6951/25000 : ℝ)^8337 ≤ (54584769469857079/10000000000000000000 : ℝ)^2048 := by
      have hnat : (6951 : ℕ)^8337*10000000000000000000^2048 ≤ 54584769469857079^2048*25000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6951 25000 54584769469857079 10000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6951/25000 : ℝ)) (X := (54584769469857079/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000022376839353/50000000000000000000 : ℝ) ≤ (10000000001099383/10000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (50000000022376839353/50000000000000000000 : ℝ)^2048 ≤ (10000000001099383/10000000000000000 : ℝ)^8337 := by
      have hnat : (50000000022376839353 : ℕ)^2048*10000000000000000^8337 ≤ 10000000001099383^8337*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000022376839353 50000000000000000000 10000000001099383 10000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000001099383/10000000000000000 : ℝ)) (X := (50000000022376839353/50000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100545847717075410143/100000000000000000000 : ℝ) ≤ (5006690667647901/5000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (100545847717075410143/100000000000000000000 : ℝ)^2048 ≤ (5006690667647901/5000000000000000 : ℝ)^8337 := by
      have hnat : (100545847717075410143 : ℕ)^2048*5000000000000000^8337 ≤ 5006690667647901^8337*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100545847717075410143 100000000000000000000 5006690667647901 5000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006690667647901/5000000000000000 : ℝ)) (X := (100545847717075410143/100000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5054584769469857079/5000000000000000000 : ℝ) ≤ (10026762669492221/10000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (5054584769469857079/5000000000000000000 : ℝ)^2048 ≤ (10026762669492221/10000000000000000 : ℝ)^8337 := by
      have hnat : (5054584769469857079 : ℕ)^2048*10000000000000000^8337 ≤ 10026762669492221^8337*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5054584769469857079 5000000000000000000 10026762669492221 10000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026762669492221/10000000000000000 : ℝ)) (X := (5054584769469857079/5000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(22376839353/100000000000000000000 : ℝ) ≤ ((45628099855560593131/45630000000000000000 : ℝ)+2*(13381334196419/2737800000000000 : ℝ)*(213/50000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (45628099855560593131/45630000000000000000 : ℝ)+2*(13381334196419/2737800000000000 : ℝ)*(213/50000 : ℝ)=(10000000001099383/10000000000000000 : ℝ) by norm_num, show 1+2*(22376839353/100000000000000000000 : ℝ)=(50000000022376839353/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54584769469857079/10000000000000000000 : ℝ)+(22376839353/100000000000000000000 : ℝ) ≤ ((45628099855560593131/45630000000000000000 : ℝ)+(13381334196419/2737800000000000 : ℝ)*((6951/25000 : ℝ)+(213/50000 : ℝ)))^(8337/2048 : ℝ) := by
    rw [show (45628099855560593131/45630000000000000000 : ℝ)+(13381334196419/2737800000000000 : ℝ)*((6951/25000 : ℝ)+(213/50000 : ℝ))=(5006690667647901/5000000000000000 : ℝ) by norm_num, show 1+(54584769469857079/10000000000000000000 : ℝ)+(22376839353/100000000000000000000 : ℝ)=(100545847717075410143/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54584769469857079/10000000000000000000 : ℝ) ≤ ((45628099855560593131/45630000000000000000 : ℝ)+2*(13381334196419/2737800000000000 : ℝ)*(6951/25000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (45628099855560593131/45630000000000000000 : ℝ)+2*(13381334196419/2737800000000000 : ℝ)*(6951/25000 : ℝ)=(10026762669492221/10000000000000000 : ℝ) by norm_num, show 1+2*(54584769469857079/10000000000000000000 : ℝ)=(5054584769469857079/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45628099855560593131/45630000000000000000 : ℝ)*(X 1 0+X 2 0)+(13381334196419/2737800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (213/50000 : ℝ)) (hi := (6951/25000 : ℝ)) (c := (45628099855560593131/45630000000000000000 : ℝ)) (alpha := (13381334196419/2737800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45628099855560593131/45630000000000000000 : ℝ)*(X 0 1+X 2 1)+(13381334196419/2737800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (213/50000 : ℝ)) (hi := (6951/25000 : ℝ)) (c := (45628099855560593131/45630000000000000000 : ℝ)) (alpha := (13381334196419/2737800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45628099855560593131/45630000000000000000 : ℝ)*(X 0 2+X 1 2)+(13381334196419/2737800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (213/50000 : ℝ)) (hi := (6951/25000 : ℝ)) (c := (45628099855560593131/45630000000000000000 : ℝ)) (alpha := (13381334196419/2737800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-261913021/1250000000 : ℝ)*X 0 0+(142517897/250000000 : ℝ)*X 0 1+(5002890293/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2709480231/5000000000 : ℝ)*X 1 0+(-617958077/2500000000 : ℝ)*X 1 1+(5002889543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5418962441/10000000000 : ℝ)*X 2 0+(5002887783/10000000000 : ℝ)*X 2 1+(-1235915983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317182589/10000000000 : ℝ)*X 0 0+(1838794109/5000000000 : ℝ)*X 0 1+(633338529/1250000000 : ℝ)*X 0 2+(4317182589/10000000000 : ℝ)*X 1 0+(1838794109/5000000000 : ℝ)*X 1 1+(633338529/1250000000 : ℝ)*X 1 2+(4317182589/10000000000 : ℝ)*X 2 0+(1838794109/5000000000 : ℝ)*X 2 1+(633338529/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2096110821/10000000000 : ℝ)*X 0 0+(1002481573/2000000000 : ℝ)*X 0 1+(5691006601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5240023219/10000000000 : ℝ)*X 1 0+(-35674221/200000000 : ℝ)*X 1 1+(569101029/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2620010897/5000000000 : ℝ)*X 2 0+(5691012163/10000000000 : ℝ)*X 2 1+(-1783710341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4318777801/10000000000 : ℝ)*X 0 0+(5047762257/10000000000 : ℝ)*X 0 1+(3696907541/10000000000 : ℝ)*X 0 2+(4318777801/10000000000 : ℝ)*X 1 0+(5047762257/10000000000 : ℝ)*X 1 1+(3696907541/10000000000 : ℝ)*X 1 2+(4318777801/10000000000 : ℝ)*X 2 0+(5047762257/10000000000 : ℝ)*X 2 1+(3696907541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5093525184117955700444178323/760500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146853301/25000000000000 : ℝ)*(base1) + (132407879/12500000000000 : ℝ)*(base19) + (203844177/12500000000000 : ℝ)*(base23) + (12246927/25000000000000 : ℝ)*(upper3) + (80782597/100000000000000 : ℝ)*(upper5) + (1076453283944967/100000000000000 : ℝ)*(major0) + (1076453283944967/100000000000000 : ℝ)*(major1) + (1076453283944967/100000000000000 : ℝ)*(major2) + (44781998512541/3125000000000 : ℝ)*(sp0) + (1433023453569507/100000000000000 : ℝ)*(sp1) + (143302434029219/10000000000000 : ℝ)*(sp2) + (719879786177767/100000000000000 : ℝ)*(sp3) + (1303028749/50000000000000 : ℝ)*(sp4) + (1458213067/100000000000000 : ℝ)*(sp5) + (719880373590971/100000000000000 : ℝ)*(f.failure) + (716512985522803/50000000000000 : ℝ)*(f.sum) + (66990134791321/45630000000000000000000000000 : ℝ)*base65 + (7320517393466228323/4563000000000000000000000000000000 : ℝ)*base68 + (11816334446847771677/4563000000000000000000000000000000 : ℝ)*base69 + (19308565931091771677/4563000000000000000000000000000000 : ℝ)*base71 + (151175209496609/45630000000000000000000000000 : ℝ)*base74 + (10198221561276771677/4563000000000000000000000000000000 : ℝ)*base75 + (19105052101962771677/4563000000000000000000000000000000 : ℝ)*base77 + (2450237855186228323/4563000000000000000000000000000000 : ℝ)*base80 + (37372253229871/45630000000000000000000000000 : ℝ)*base81 + (18928021/2000000000000000000000 : ℝ)*base90 + (18928021/2000000000000000000000 : ℝ)*base92 + (18928021/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (568412931097731729793266389/380250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37955597/1562500000000 : ℝ)*(base19) + (381415773/12500000000000 : ℝ)*(base23) + (430910371/100000000000000 : ℝ)*(upper2) + (12784469/2000000000000 : ℝ)*(upper3) + (405781441/100000000000000 : ℝ)*(upper5) + (1106945922165081/100000000000000 : ℝ)*(major0) + (1106945922165081/100000000000000 : ℝ)*(major1) + (1106945922165081/100000000000000 : ℝ)*(major2) + (13821942233/100000000000000 : ℝ)*(sp1) + (1969499119/10000000000000 : ℝ)*(sp2) + (1473619405650453/100000000000000 : ℝ)*(sp4) + (368400788637503/25000000000000 : ℝ)*(sp5) + (36839916483327/2500000000000 : ℝ)*(sp6) + (740272388851703/100000000000000 : ℝ)*(sp7) + (740272388851703/100000000000000 : ℝ)*(f.failure) + (1473619405650453/100000000000000 : ℝ)*(f.sum) + (70882734911387/45630000000000000000000000000 : ℝ)*base66 + (44359814004964308611/4563000000000000000000000000000000 : ℝ)*base67 + (11536119633184308611/4563000000000000000000000000000000 : ℝ)*base69 + (9106172462221308611/4563000000000000000000000000000000 : ℝ)*base71 + (55426392829903/45630000000000000000000000000 : ℝ)*base73 + (32910339853186308611/4563000000000000000000000000000000 : ℝ)*base75 + (8698605137953308611/4563000000000000000000000000000000 : ℝ)*base77 + (3249939208330691389/4563000000000000000000000000000000 : ℝ)*base80 + (113822358763577/45630000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4332647/2000000000000000000000 : ℝ)*base89 + (4332647/2000000000000000000000 : ℝ)*base91 + (4332647/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1145_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6951/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2833/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2553/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1145_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1145_s2_0 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2148378991/10000000000 : ℝ)*x 0 + (5510247799/10000000000 : ℝ)*x 1 + (2579802933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148378991/10000000000 : ℝ)^4169 ≤ (6510566173893/50000000000000 : ℝ)^3145 := by
    have hnat : (2148378991 : ℕ)^4169*50000000000000^3145 ≤ 6510566173893^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148378991 10000000000 6510566173893 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510247799/10000000000 : ℝ)^4169 ≤ (45383442664411/100000000000000 : ℝ)^3145 := by
    have hnat : (5510247799 : ℕ)^4169*100000000000000^3145 ≤ 45383442664411^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510247799 10000000000 45383442664411 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2579802933/5000000000 : ℝ)^4169 ≤ (20797712489853/50000000000000 : ℝ)^3145 := by
    have hnat : (2579802933 : ℕ)^4169*50000000000000^3145 ≤ 20797712489853^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579802933 5000000000 20797712489853 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2148378991/10000000000 : ℝ), (5510247799/10000000000 : ℝ), (2579802933/5000000000 : ℝ)] ![(6510566173893/50000000000000 : ℝ), (45383442664411/100000000000000 : ℝ), (20797712489853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2148378991/10000000000 : ℝ)|^4169 ≤ (6510566173893/50000000000000 : ℝ)^3145
        have hw : |(-2148378991/10000000000 : ℝ)|=(2148378991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510247799/10000000000 : ℝ)|^4169 ≤ (45383442664411/100000000000000 : ℝ)^3145
        have hw : |(5510247799/10000000000 : ℝ)|=(5510247799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2579802933/5000000000 : ℝ)|^4169 ≤ (20797712489853/50000000000000 : ℝ)^3145
        have hw : |(2579802933/5000000000 : ℝ)|=(2579802933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s2_1 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373737417/10000000000 : ℝ)*x 0 + (-36416513/156250000 : ℝ)*x 1 + (1289901997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373737417/10000000000 : ℝ)^4169 ≤ (8779817229949/20000000000000 : ℝ)^3145 := by
    have hnat : (5373737417 : ℕ)^4169*20000000000000^3145 ≤ 8779817229949^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373737417 10000000000 8779817229949 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36416513/156250000 : ℝ)^4169 ≤ (14505466178027/100000000000000 : ℝ)^3145 := by
    have hnat : (36416513 : ℕ)^4169*100000000000000^3145 ≤ 14505466178027^3145*156250000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36416513 156250000 14505466178027 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1289901997/2500000000 : ℝ)^4169 ≤ (41595447656711/100000000000000 : ℝ)^3145 := by
    have hnat : (1289901997 : ℕ)^4169*100000000000000^3145 ≤ 41595447656711^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289901997 2500000000 41595447656711 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373737417/10000000000 : ℝ), (-36416513/156250000 : ℝ), (1289901997/2500000000 : ℝ)] ![(8779817229949/20000000000000 : ℝ), (14505466178027/100000000000000 : ℝ), (41595447656711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373737417/10000000000 : ℝ)|^4169 ≤ (8779817229949/20000000000000 : ℝ)^3145
        have hw : |(5373737417/10000000000 : ℝ)|=(5373737417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36416513/156250000 : ℝ)|^4169 ≤ (14505466178027/100000000000000 : ℝ)^3145
        have hw : |(-36416513/156250000 : ℝ)|=(36416513/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1289901997/2500000000 : ℝ)|^4169 ≤ (41595447656711/100000000000000 : ℝ)^3145
        have hw : |(1289901997/2500000000 : ℝ)|=(1289901997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s2_2 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107474749/200000000 : ℝ)*x 0 + (644950973/1250000000 : ℝ)*x 1 + (-1165328527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107474749/200000000 : ℝ)^4169 ≤ (1371846453347/3125000000000 : ℝ)^3145 := by
    have hnat : (107474749 : ℕ)^4169*3125000000000^3145 ≤ 1371846453347^3145*200000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107474749 200000000 1371846453347 3125000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (644950973/1250000000 : ℝ)^4169 ≤ (259971534229/625000000000 : ℝ)^3145 := by
    have hnat : (644950973 : ℕ)^4169*625000000000^3145 ≤ 259971534229^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644950973 1250000000 259971534229 625000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1165328527/5000000000 : ℝ)^4169 ≤ (3626367002393/25000000000000 : ℝ)^3145 := by
    have hnat : (1165328527 : ℕ)^4169*25000000000000^3145 ≤ 3626367002393^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165328527 5000000000 3626367002393 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107474749/200000000 : ℝ), (644950973/1250000000 : ℝ), (-1165328527/5000000000 : ℝ)] ![(1371846453347/3125000000000 : ℝ), (259971534229/625000000000 : ℝ), (3626367002393/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107474749/200000000 : ℝ)|^4169 ≤ (1371846453347/3125000000000 : ℝ)^3145
        have hw : |(107474749/200000000 : ℝ)|=(107474749/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(644950973/1250000000 : ℝ)|^4169 ≤ (259971534229/625000000000 : ℝ)^3145
        have hw : |(644950973/1250000000 : ℝ)|=(644950973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1165328527/5000000000 : ℝ)|^4169 ≤ (3626367002393/25000000000000 : ℝ)^3145
        have hw : |(-1165328527/5000000000 : ℝ)|=(1165328527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s2_3 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (870720001/2000000000 : ℝ)*x 0 + (2009226911/5000000000 : ℝ)*x 1 + (1179113149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870720001/2000000000 : ℝ)^4169 ≤ (33209243506647/100000000000000 : ℝ)^3145 := by
    have hnat : (870720001 : ℕ)^4169*100000000000000^3145 ≤ 33209243506647^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870720001 2000000000 33209243506647 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009226911/5000000000 : ℝ)^4169 ≤ (29863595693591/100000000000000 : ℝ)^3145 := by
    have hnat : (2009226911 : ℕ)^4169*100000000000000^3145 ≤ 29863595693591^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009226911 5000000000 29863595693591 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1179113149/2500000000 : ℝ)^4169 ≤ (2307947549273/6250000000000 : ℝ)^3145 := by
    have hnat : (1179113149 : ℕ)^4169*6250000000000^3145 ≤ 2307947549273^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179113149 2500000000 2307947549273 6250000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870720001/2000000000 : ℝ), (2009226911/5000000000 : ℝ), (1179113149/2500000000 : ℝ)] ![(33209243506647/100000000000000 : ℝ), (29863595693591/100000000000000 : ℝ), (2307947549273/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870720001/2000000000 : ℝ)|^4169 ≤ (33209243506647/100000000000000 : ℝ)^3145
        have hw : |(870720001/2000000000 : ℝ)|=(870720001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2009226911/5000000000 : ℝ)|^4169 ≤ (29863595693591/100000000000000 : ℝ)^3145
        have hw : |(2009226911/5000000000 : ℝ)|=(2009226911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1179113149/2500000000 : ℝ)|^4169 ≤ (2307947549273/6250000000000 : ℝ)^3145
        have hw : |(1179113149/2500000000 : ℝ)|=(1179113149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s2_4 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-33570013/156250000 : ℝ)*x 0 + (206480759/400000000 : ℝ)*x 1 + (11015621/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33570013/156250000 : ℝ)^4169 ≤ (13021950577239/100000000000000 : ℝ)^3145 := by
    have hnat : (33570013 : ℕ)^4169*100000000000000^3145 ≤ 13021950577239^3145*156250000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33570013 156250000 13021950577239 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206480759/400000000 : ℝ)^4169 ≤ (41621214916927/100000000000000 : ℝ)^3145 := by
    have hnat : (206480759 : ℕ)^4169*100000000000000^3145 ≤ 41621214916927^3145*400000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206480759 400000000 41621214916927 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11015621/20000000 : ℝ)^4169 ≤ (11339208622391/25000000000000 : ℝ)^3145 := by
    have hnat : (11015621 : ℕ)^4169*25000000000000^3145 ≤ 11339208622391^3145*20000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11015621 20000000 11339208622391 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33570013/156250000 : ℝ), (206480759/400000000 : ℝ), (11015621/20000000 : ℝ)] ![(13021950577239/100000000000000 : ℝ), (41621214916927/100000000000000 : ℝ), (11339208622391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33570013/156250000 : ℝ)|^4169 ≤ (13021950577239/100000000000000 : ℝ)^3145
        have hw : |(-33570013/156250000 : ℝ)|=(33570013/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(206480759/400000000 : ℝ)|^4169 ≤ (41621214916927/100000000000000 : ℝ)^3145
        have hw : |(206480759/400000000 : ℝ)|=(206480759/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11015621/20000000 : ℝ)|^4169 ≤ (11339208622391/25000000000000 : ℝ)^3145
        have hw : |(11015621/20000000 : ℝ)|=(11015621/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s2_5 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642376259/5000000000 : ℝ)*x 0 + (-123903261/625000000 : ℝ)*x 1 + (1376952801/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642376259/5000000000 : ℝ)^4169 ≤ (42938071874459/100000000000000 : ℝ)^3145 := by
    have hnat : (2642376259 : ℕ)^4169*100000000000000^3145 ≤ 42938071874459^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642376259 5000000000 42938071874459 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123903261/625000000 : ℝ)^4169 ≤ (11705085930859/100000000000000 : ℝ)^3145 := by
    have hnat : (123903261 : ℕ)^4169*100000000000000^3145 ≤ 11705085930859^3145*625000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123903261 625000000 11705085930859 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376952801/2500000000 : ℝ)^4169 ≤ (45356842174631/100000000000000 : ℝ)^3145 := by
    have hnat : (1376952801 : ℕ)^4169*100000000000000^3145 ≤ 45356842174631^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376952801 2500000000 45356842174631 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642376259/5000000000 : ℝ), (-123903261/625000000 : ℝ), (1376952801/2500000000 : ℝ)] ![(42938071874459/100000000000000 : ℝ), (11705085930859/100000000000000 : ℝ), (45356842174631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642376259/5000000000 : ℝ)|^4169 ≤ (42938071874459/100000000000000 : ℝ)^3145
        have hw : |(2642376259/5000000000 : ℝ)|=(2642376259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123903261/625000000 : ℝ)|^4169 ≤ (11705085930859/100000000000000 : ℝ)^3145
        have hw : |(-123903261/625000000 : ℝ)|=(123903261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1376952801/2500000000 : ℝ)|^4169 ≤ (45356842174631/100000000000000 : ℝ)^3145
        have hw : |(1376952801/2500000000 : ℝ)|=(1376952801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s2_6 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642375481/5000000000 : ℝ)*x 0 + (5507810977/10000000000 : ℝ)*x 1 + (-991227317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642375481/5000000000 : ℝ)^4169 ≤ (21469027557911/50000000000000 : ℝ)^3145 := by
    have hnat : (2642375481 : ℕ)^4169*50000000000000^3145 ≤ 21469027557911^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642375481 5000000000 21469027557911 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5507810977/10000000000 : ℝ)^4169 ≤ (45356839696633/100000000000000 : ℝ)^3145 := by
    have hnat : (5507810977 : ℕ)^4169*100000000000000^3145 ≤ 45356839696633^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507810977 10000000000 45356839696633 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (991227317/5000000000 : ℝ)^4169 ≤ (182892268267/1562500000000 : ℝ)^3145 := by
    have hnat : (991227317 : ℕ)^4169*1562500000000^3145 ≤ 182892268267^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991227317 5000000000 182892268267 1562500000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642375481/5000000000 : ℝ), (5507810977/10000000000 : ℝ), (-991227317/5000000000 : ℝ)] ![(21469027557911/50000000000000 : ℝ), (45356839696633/100000000000000 : ℝ), (182892268267/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642375481/5000000000 : ℝ)|^4169 ≤ (21469027557911/50000000000000 : ℝ)^3145
        have hw : |(2642375481/5000000000 : ℝ)|=(2642375481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5507810977/10000000000 : ℝ)|^4169 ≤ (45356839696633/100000000000000 : ℝ)^3145
        have hw : |(5507810977/10000000000 : ℝ)|=(5507810977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-991227317/5000000000 : ℝ)|^4169 ≤ (182892268267/1562500000000 : ℝ)^3145
        have hw : |(-991227317/5000000000 : ℝ)|=(991227317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s2_7 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353801751/10000000000 : ℝ)*x 0 + (4711650771/10000000000 : ℝ)*x 1 + (4023303823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353801751/10000000000 : ℝ)^4169 ≤ (4151410438181/12500000000000 : ℝ)^3145 := by
    have hnat : (4353801751 : ℕ)^4169*12500000000000^3145 ≤ 4151410438181^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353801751 10000000000 4151410438181 12500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4711650771/10000000000 : ℝ)^4169 ≤ (36877332494993/100000000000000 : ℝ)^3145 := by
    have hnat : (4711650771 : ℕ)^4169*100000000000000^3145 ≤ 36877332494993^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4711650771 10000000000 36877332494993 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023303823/10000000000 : ℝ)^4169 ≤ (29911383983551/100000000000000 : ℝ)^3145 := by
    have hnat : (4023303823 : ℕ)^4169*100000000000000^3145 ≤ 29911383983551^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023303823 10000000000 29911383983551 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353801751/10000000000 : ℝ), (4711650771/10000000000 : ℝ), (4023303823/10000000000 : ℝ)] ![(4151410438181/12500000000000 : ℝ), (36877332494993/100000000000000 : ℝ), (29911383983551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353801751/10000000000 : ℝ)|^4169 ≤ (4151410438181/12500000000000 : ℝ)^3145
        have hw : |(4353801751/10000000000 : ℝ)|=(4353801751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4711650771/10000000000 : ℝ)|^4169 ≤ (36877332494993/100000000000000 : ℝ)^3145
        have hw : |(4711650771/10000000000 : ℝ)|=(4711650771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023303823/10000000000 : ℝ)|^4169 ≤ (29911383983551/100000000000000 : ℝ)^3145
        have hw : |(4023303823/10000000000 : ℝ)|=(4023303823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1145_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2553/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2271/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8247/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2553/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2833/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2553/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2833/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2553/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2833/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2553/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2833/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2553/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2833/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2553/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2833/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (2833/50000 : ℝ) ^ (8337/2048 : ℝ) ≤ (52567497805873/6250000000000000000 : ℝ) := by
    have hpowers : (2833/50000 : ℝ)^8337 ≤ (52567497805873/6250000000000000000 : ℝ)^2048 := by
      have hnat : (2833 : ℕ)^8337*6250000000000000000^2048 ≤ 52567497805873^2048*50000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2833 50000 52567497805873 6250000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2833/50000 : ℝ)) (X := (52567497805873/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2553/12500 : ℝ) ^ (8337/2048 : ℝ) ≤ (7774825337699127/5000000000000000000 : ℝ) := by
    have hpowers : (2553/12500 : ℝ)^8337 ≤ (7774825337699127/5000000000000000000 : ℝ)^2048 := by
      have hnat : (2553 : ℕ)^8337*5000000000000000000^2048 ≤ 7774825337699127^2048*12500^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2553 12500 7774825337699127 5000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2553/12500 : ℝ)) (X := (7774825337699127/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125052567497805873/3125000000000000000 : ℝ) ≤ (2500010330579581/2500000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (3125052567497805873/3125000000000000000 : ℝ)^2048 ≤ (2500010330579581/2500000000000000 : ℝ)^8337 := by
      have hnat : (3125052567497805873 : ℕ)^2048*2500000000000000^8337 ≤ 2500010330579581^8337*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125052567497805873 3125000000000000000 2500010330579581 2500000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500010330579581/2500000000000000 : ℝ)) (X := (3125052567497805873/3125000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25039084396679719127/25000000000000000000 : ℝ) ≤ (5001919100105033/5000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (25039084396679719127/25000000000000000000 : ℝ)^2048 ≤ (5001919100105033/5000000000000000 : ℝ)^8337 := by
      have hnat : (25039084396679719127 : ℕ)^2048*5000000000000000^8337 ≤ 5001919100105033^8337*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25039084396679719127 25000000000000000000 5001919100105033 5000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001919100105033/5000000000000000 : ℝ)) (X := (25039084396679719127/25000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2507774825337699127/2500000000000000000 : ℝ) ≤ (625477192381363/625000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (2507774825337699127/2500000000000000000 : ℝ)^2048 ≤ (625477192381363/625000000000000 : ℝ)^8337 := by
      have hnat : (2507774825337699127 : ℕ)^2048*625000000000000^8337 ≤ 625477192381363^8337*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2507774825337699127 2500000000000000000 625477192381363 625000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625477192381363/625000000000000 : ℝ)) (X := (2507774825337699127/2500000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(52567497805873/6250000000000000000 : ℝ) ≤ ((2305274743976634457/2305937500000000000 : ℝ)+2*(1898438945871/737900000000000 : ℝ)*(2833/50000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (2305274743976634457/2305937500000000000 : ℝ)+2*(1898438945871/737900000000000 : ℝ)*(2833/50000 : ℝ)=(2500010330579581/2500000000000000 : ℝ) by norm_num, show 1+2*(52567497805873/6250000000000000000 : ℝ)=(3125052567497805873/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7774825337699127/5000000000000000000 : ℝ)+(52567497805873/6250000000000000000 : ℝ) ≤ ((2305274743976634457/2305937500000000000 : ℝ)+(1898438945871/737900000000000 : ℝ)*((2553/12500 : ℝ)+(2833/50000 : ℝ)))^(8337/2048 : ℝ) := by
    rw [show (2305274743976634457/2305937500000000000 : ℝ)+(1898438945871/737900000000000 : ℝ)*((2553/12500 : ℝ)+(2833/50000 : ℝ))=(5001919100105033/5000000000000000 : ℝ) by norm_num, show 1+(7774825337699127/5000000000000000000 : ℝ)+(52567497805873/6250000000000000000 : ℝ)=(25039084396679719127/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7774825337699127/5000000000000000000 : ℝ) ≤ ((2305274743976634457/2305937500000000000 : ℝ)+2*(1898438945871/737900000000000 : ℝ)*(2553/12500 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (2305274743976634457/2305937500000000000 : ℝ)+2*(1898438945871/737900000000000 : ℝ)*(2553/12500 : ℝ)=(625477192381363/625000000000000 : ℝ) by norm_num, show 1+2*(7774825337699127/5000000000000000000 : ℝ)=(2507774825337699127/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2305274743976634457/2305937500000000000 : ℝ)*(X 1 0+X 2 0)+(1898438945871/737900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2833/50000 : ℝ)) (hi := (2553/12500 : ℝ)) (c := (2305274743976634457/2305937500000000000 : ℝ)) (alpha := (1898438945871/737900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2305274743976634457/2305937500000000000 : ℝ)*(X 0 1+X 2 1)+(1898438945871/737900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2833/50000 : ℝ)) (hi := (2553/12500 : ℝ)) (c := (2305274743976634457/2305937500000000000 : ℝ)) (alpha := (1898438945871/737900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2305274743976634457/2305937500000000000 : ℝ)*(X 0 2+X 1 2)+(1898438945871/737900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2833/50000 : ℝ)) (hi := (2553/12500 : ℝ)) (c := (2305274743976634457/2305937500000000000 : ℝ)) (alpha := (1898438945871/737900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2148378991/10000000000 : ℝ)*X 0 0+(5510247799/10000000000 : ℝ)*X 0 1+(2579802933/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5373737417/10000000000 : ℝ)*X 1 0+(-36416513/156250000 : ℝ)*X 1 1+(1289901997/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((107474749/200000000 : ℝ)*X 2 0+(644950973/1250000000 : ℝ)*X 2 1+(-1165328527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870720001/2000000000 : ℝ)*X 0 0+(2009226911/5000000000 : ℝ)*X 0 1+(1179113149/2500000000 : ℝ)*X 0 2+(870720001/2000000000 : ℝ)*X 1 0+(2009226911/5000000000 : ℝ)*X 1 1+(1179113149/2500000000 : ℝ)*X 1 2+(870720001/2000000000 : ℝ)*X 2 0+(2009226911/5000000000 : ℝ)*X 2 1+(1179113149/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-33570013/156250000 : ℝ)*X 0 0+(206480759/400000000 : ℝ)*X 0 1+(11015621/20000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642376259/5000000000 : ℝ)*X 1 0+(-123903261/625000000 : ℝ)*X 1 1+(1376952801/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2642375481/5000000000 : ℝ)*X 2 0+(5507810977/10000000000 : ℝ)*X 2 1+(-991227317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353801751/10000000000 : ℝ)*X 0 0+(4711650771/10000000000 : ℝ)*X 0 1+(4023303823/10000000000 : ℝ)*X 0 2+(4353801751/10000000000 : ℝ)*X 1 0+(4711650771/10000000000 : ℝ)*X 1 1+(4023303823/10000000000 : ℝ)*X 1 2+(4353801751/10000000000 : ℝ)*X 2 0+(4711650771/10000000000 : ℝ)*X 2 1+(4023303823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (363814753053457550384950929/115296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (251430381/100000000000000 : ℝ)*(base15) + (4178003/100000000000000 : ℝ)*(base29) + (33736571/20000000000000 : ℝ)*(upper2) + (22682349/25000000000000 : ℝ)*(upper3) + (15443989/25000000000000 : ℝ)*(upper4) + (53557618576199/2500000000000 : ℝ)*(major0) + (535576186806491/25000000000000 : ℝ)*(major1) + (535576186806491/25000000000000 : ℝ)*(major2) + (2851927644534327/100000000000000 : ℝ)*(sp0) + (1425969188054773/50000000000000 : ℝ)*(sp1) + (1425969313769963/50000000000000 : ℝ)*(sp2) + (179083653500473/12500000000000 : ℝ)*(sp3) + (10987183603/100000000000000 : ℝ)*(sp4) + (191193523/12500000000000 : ℝ)*(sp7) + (1432670757551967/100000000000000 : ℝ)*(f.failure) + (285193863171793/10000000000000 : ℝ)*(f.sum) + (114260352379499/36895000000000000000000000000 : ℝ)*base65 + (359220942917089613/57648437500000000000000000000000 : ℝ)*base68 + (69438491481566637/57648437500000000000000000000000 : ℝ)*base69 + (16989837043625733/1441210937500000000000000000000 : ℝ)*base72 + (83042667360949/18447500000000000000000000000 : ℝ)*base74 + (12670568639233363/57648437500000000000000000000000 : ℝ)*base76 + (83866146765915239/11529687500000000000000000000000 : ℝ)*base78 + (284985193401795863/57648437500000000000000000000000 : ℝ)*base80 + (5675074506281/18447500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5935183/2000000000000000000000 : ℝ)*base89 + (14064817/2000000000000000000000 : ℝ)*base92 + (14064817/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1130433075338896926526519023/115296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1722378613/100000000000000 : ℝ)*(base19) + (583083539/50000000000000 : ℝ)*(base23) + (41143567/12500000000000 : ℝ)*(upper2) + (108943417/100000000000000 : ℝ)*(upper3) + (149331571/50000000000000 : ℝ)*(upper5) + (1086165536667169/50000000000000 : ℝ)*(major0) + (1086165536667169/50000000000000 : ℝ)*(major1) + (1086165536667169/50000000000000 : ℝ)*(major2) + (12469329121/50000000000000 : ℝ)*(sp1) + (5484538873/100000000000000 : ℝ)*(sp2) + (722977723558239/25000000000000 : ℝ)*(sp4) + (1445942116598051/50000000000000 : ℝ)*(sp5) + (1445952121763503/50000000000000 : ℝ)*(sp6) + (1452750925617641/100000000000000 : ℝ)*(sp7) + (1452750925617641/100000000000000 : ℝ)*(f.failure) + (722977723558239/25000000000000 : ℝ)*(f.sum) + (124975435394707/36895000000000000000000000000 : ℝ)*base66 + (488182853654335983/115296875000000000000000000000000 : ℝ)*base67 + (148104547967960983/115296875000000000000000000000000 : ℝ)*base69 + (224515996995195267/115296875000000000000000000000000 : ℝ)*base72 + (75724734274473/36895000000000000000000000000 : ℝ)*base73 + (1033357046494789017/115296875000000000000000000000000 : ℝ)*base76 + (340879122737195267/115296875000000000000000000000000 : ℝ)*base78 + (512800655713257767/115296875000000000000000000000000 : ℝ)*base80 + (133494494267083/36895000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (14066809/2000000000000000000000 : ℝ)*base89 + (14066809/2000000000000000000000 : ℝ)*base91 + (14066809/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1145_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2553/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1145_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1145_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1145_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1145_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1145_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1145_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
