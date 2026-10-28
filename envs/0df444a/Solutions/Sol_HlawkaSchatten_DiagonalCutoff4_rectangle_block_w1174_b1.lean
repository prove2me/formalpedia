-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1174_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:46:49.767863+00:00
-- url     : https://prove2.me/submissions/972601b8-bc9c-45e1-b96c-99967d7493b0

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
theorem support_rectangle_w1174_s3_0 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-429642457/2000000000 : ℝ)*x 0 + (5425965909/10000000000 : ℝ)*x 1 + (209399903/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429642457/2000000000 : ℝ)^8367 ≤ (3262437081433/25000000000000 : ℝ)^6319 := by
    have hnat : (429642457 : ℕ)^8367*25000000000000^6319 ≤ 3262437081433^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429642457 2000000000 3262437081433 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425965909/10000000000 : ℝ)^8367 ≤ (44506205384393/100000000000000 : ℝ)^6319 := by
    have hnat : (5425965909 : ℕ)^8367*100000000000000^6319 ≤ 44506205384393^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425965909 10000000000 44506205384393 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209399903/400000000 : ℝ)^8367 ≤ (42444046273191/100000000000000 : ℝ)^6319 := by
    have hnat : (209399903 : ℕ)^8367*100000000000000^6319 ≤ 42444046273191^6319*400000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209399903 400000000 42444046273191 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429642457/2000000000 : ℝ), (5425965909/10000000000 : ℝ), (209399903/400000000 : ℝ)] ![(3262437081433/25000000000000 : ℝ), (44506205384393/100000000000000 : ℝ), (42444046273191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429642457/2000000000 : ℝ)|^8367 ≤ (3262437081433/25000000000000 : ℝ)^6319
        have hw : |(-429642457/2000000000 : ℝ)|=(429642457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425965909/10000000000 : ℝ)|^8367 ≤ (44506205384393/100000000000000 : ℝ)^6319
        have hw : |(5425965909/10000000000 : ℝ)|=(5425965909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209399903/400000000 : ℝ)|^8367 ≤ (42444046273191/100000000000000 : ℝ)^6319
        have hw : |(209399903/400000000 : ℝ)|=(209399903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s3_1 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353035329/10000000000 : ℝ)*x 0 + (-1122881139/5000000000 : ℝ)*x 1 + (5234997377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353035329/10000000000 : ℝ)^8367 ≤ (43715845810457/100000000000000 : ℝ)^6319 := by
    have hnat : (5353035329 : ℕ)^8367*100000000000000^6319 ≤ 43715845810457^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353035329 10000000000 43715845810457 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122881139/5000000000 : ℝ)^8367 ≤ (6920055012643/50000000000000 : ℝ)^6319 := by
    have hnat : (1122881139 : ℕ)^8367*50000000000000^6319 ≤ 6920055012643^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122881139 5000000000 6920055012643 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234997377/10000000000 : ℝ)^8367 ≤ (10611011036891/25000000000000 : ℝ)^6319 := by
    have hnat : (5234997377 : ℕ)^8367*25000000000000^6319 ≤ 10611011036891^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234997377 10000000000 10611011036891 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353035329/10000000000 : ℝ), (-1122881139/5000000000 : ℝ), (5234997377/10000000000 : ℝ)] ![(43715845810457/100000000000000 : ℝ), (6920055012643/50000000000000 : ℝ), (10611011036891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353035329/10000000000 : ℝ)|^8367 ≤ (43715845810457/100000000000000 : ℝ)^6319
        have hw : |(5353035329/10000000000 : ℝ)|=(5353035329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1122881139/5000000000 : ℝ)|^8367 ≤ (6920055012643/50000000000000 : ℝ)^6319
        have hw : |(-1122881139/5000000000 : ℝ)|=(1122881139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234997377/10000000000 : ℝ)|^8367 ≤ (10611011036891/25000000000000 : ℝ)^6319
        have hw : |(5234997377/10000000000 : ℝ)|=(5234997377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s3_2 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070607083/2000000000 : ℝ)*x 0 + (1046999473/2000000000 : ℝ)*x 1 + (-112288109/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070607083/2000000000 : ℝ)^8367 ≤ (8743169348081/20000000000000 : ℝ)^6319 := by
    have hnat : (1070607083 : ℕ)^8367*20000000000000^6319 ≤ 8743169348081^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070607083 2000000000 8743169348081 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046999473/2000000000 : ℝ)^8367 ≤ (42444044018739/100000000000000 : ℝ)^6319 := by
    have hnat : (1046999473 : ℕ)^8367*100000000000000^6319 ≤ 42444044018739^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046999473 2000000000 42444044018739 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112288109/500000000 : ℝ)^8367 ≤ (13840109225593/100000000000000 : ℝ)^6319 := by
    have hnat : (112288109 : ℕ)^8367*100000000000000^6319 ≤ 13840109225593^6319*500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112288109 500000000 13840109225593 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070607083/2000000000 : ℝ), (1046999473/2000000000 : ℝ), (-112288109/500000000 : ℝ)] ![(8743169348081/20000000000000 : ℝ), (42444044018739/100000000000000 : ℝ), (13840109225593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070607083/2000000000 : ℝ)|^8367 ≤ (8743169348081/20000000000000 : ℝ)^6319
        have hw : |(1070607083/2000000000 : ℝ)|=(1070607083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046999473/2000000000 : ℝ)|^8367 ≤ (42444044018739/100000000000000 : ℝ)^6319
        have hw : |(1046999473/2000000000 : ℝ)|=(1046999473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-112288109/500000000 : ℝ)|^8367 ≤ (13840109225593/100000000000000 : ℝ)^6319
        have hw : |(-112288109/500000000 : ℝ)|=(112288109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s3_3 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358122771/10000000000 : ℝ)*x 0 + (4171101713/10000000000 : ℝ)*x 1 + (4553414451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358122771/10000000000 : ℝ)^8367 ≤ (6659256150911/20000000000000 : ℝ)^6319 := by
    have hnat : (4358122771 : ℕ)^8367*20000000000000^6319 ≤ 6659256150911^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358122771 10000000000 6659256150911 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171101713/10000000000 : ℝ)^8367 ≤ (15708811754361/50000000000000 : ℝ)^6319 := by
    have hnat : (4171101713 : ℕ)^8367*50000000000000^6319 ≤ 15708811754361^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171101713 10000000000 15708811754361 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4553414451/10000000000 : ℝ)^8367 ≤ (2205380982087/6250000000000 : ℝ)^6319 := by
    have hnat : (4553414451 : ℕ)^8367*6250000000000^6319 ≤ 2205380982087^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553414451 10000000000 2205380982087 6250000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358122771/10000000000 : ℝ), (4171101713/10000000000 : ℝ), (4553414451/10000000000 : ℝ)] ![(6659256150911/20000000000000 : ℝ), (15708811754361/50000000000000 : ℝ), (2205380982087/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358122771/10000000000 : ℝ)|^8367 ≤ (6659256150911/20000000000000 : ℝ)^6319
        have hw : |(4358122771/10000000000 : ℝ)|=(4358122771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171101713/10000000000 : ℝ)|^8367 ≤ (15708811754361/50000000000000 : ℝ)^6319
        have hw : |(4171101713/10000000000 : ℝ)|=(4171101713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4553414451/10000000000 : ℝ)|^8367 ≤ (2205380982087/6250000000000 : ℝ)^6319
        have hw : |(4553414451/10000000000 : ℝ)|=(4553414451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s3_4 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2148228811/10000000000 : ℝ)*x 0 + (5235722367/10000000000 : ℝ)*x 1 + (2712618607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148228811/10000000000 : ℝ)^8367 ≤ (13049881253173/100000000000000 : ℝ)^6319 := by
    have hnat : (2148228811 : ℕ)^8367*100000000000000^6319 ≤ 13049881253173^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148228811 10000000000 13049881253173 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235722367/10000000000 : ℝ)^8367 ≤ (21225913721049/50000000000000 : ℝ)^6319 := by
    have hnat : (5235722367 : ℕ)^8367*50000000000000^6319 ≤ 21225913721049^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235722367 10000000000 21225913721049 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712618607/5000000000 : ℝ)^8367 ≤ (44498291289411/100000000000000 : ℝ)^6319 := by
    have hnat : (2712618607 : ℕ)^8367*100000000000000^6319 ≤ 44498291289411^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712618607 5000000000 44498291289411 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2148228811/10000000000 : ℝ), (5235722367/10000000000 : ℝ), (2712618607/5000000000 : ℝ)] ![(13049881253173/100000000000000 : ℝ), (21225913721049/50000000000000 : ℝ), (44498291289411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2148228811/10000000000 : ℝ)|^8367 ≤ (13049881253173/100000000000000 : ℝ)^6319
        have hw : |(-2148228811/10000000000 : ℝ)|=(2148228811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235722367/10000000000 : ℝ)|^8367 ≤ (21225913721049/50000000000000 : ℝ)^6319
        have hw : |(5235722367/10000000000 : ℝ)|=(5235722367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712618607/5000000000 : ℝ)|^8367 ≤ (44498291289411/100000000000000 : ℝ)^6319
        have hw : |(2712618607/5000000000 : ℝ)|=(2712618607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s3_5 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530454231/1000000000 : ℝ)*x 0 + (-513880773/2500000000 : ℝ)*x 1 + (5425237059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530454231/1000000000 : ℝ)^8367 ≤ (43192245272177/100000000000000 : ℝ)^6319 := by
    have hnat : (530454231 : ℕ)^8367*100000000000000^6319 ≤ 43192245272177^6319*1000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530454231 1000000000 43192245272177 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513880773/2500000000 : ℝ)^8367 ≤ (1538683137323/12500000000000 : ℝ)^6319 := by
    have hnat : (513880773 : ℕ)^8367*12500000000000^6319 ≤ 1538683137323^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513880773 2500000000 1538683137323 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425237059/10000000000 : ℝ)^8367 ≤ (1390571550189/3125000000000 : ℝ)^6319 := by
    have hnat : (5425237059 : ℕ)^8367*3125000000000^6319 ≤ 1390571550189^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425237059 10000000000 1390571550189 3125000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530454231/1000000000 : ℝ), (-513880773/2500000000 : ℝ), (5425237059/10000000000 : ℝ)] ![(43192245272177/100000000000000 : ℝ), (1538683137323/12500000000000 : ℝ), (1390571550189/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530454231/1000000000 : ℝ)|^8367 ≤ (43192245272177/100000000000000 : ℝ)^6319
        have hw : |(530454231/1000000000 : ℝ)|=(530454231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513880773/2500000000 : ℝ)|^8367 ≤ (1538683137323/12500000000000 : ℝ)^6319
        have hw : |(-513880773/2500000000 : ℝ)|=(513880773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425237059/10000000000 : ℝ)|^8367 ≤ (1390571550189/3125000000000 : ℝ)^6319
        have hw : |(5425237059/10000000000 : ℝ)|=(5425237059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s3_6 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060908701/2000000000 : ℝ)*x 0 + (5425235971/10000000000 : ℝ)*x 1 + (-1027761479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060908701/2000000000 : ℝ)^8367 ≤ (43192258156073/100000000000000 : ℝ)^6319 := by
    have hnat : (1060908701 : ℕ)^8367*100000000000000^6319 ≤ 43192258156073^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060908701 2000000000 43192258156073 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425235971/10000000000 : ℝ)^8367 ≤ (5562284723741/12500000000000 : ℝ)^6319 := by
    have hnat : (5425235971 : ℕ)^8367*12500000000000^6319 ≤ 5562284723741^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425235971 10000000000 5562284723741 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027761479/5000000000 : ℝ)^8367 ≤ (246189280721/2000000000000 : ℝ)^6319 := by
    have hnat : (1027761479 : ℕ)^8367*2000000000000^6319 ≤ 246189280721^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027761479 5000000000 246189280721 2000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060908701/2000000000 : ℝ), (5425235971/10000000000 : ℝ), (-1027761479/5000000000 : ℝ)] ![(43192258156073/100000000000000 : ℝ), (5562284723741/12500000000000 : ℝ), (246189280721/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060908701/2000000000 : ℝ)|^8367 ≤ (43192258156073/100000000000000 : ℝ)^6319
        have hw : |(1060908701/2000000000 : ℝ)|=(1060908701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425235971/10000000000 : ℝ)|^8367 ≤ (5562284723741/12500000000000 : ℝ)^6319
        have hw : |(5425235971/10000000000 : ℝ)|=(5425235971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1027761479/5000000000 : ℝ)|^8367 ≤ (246189280721/2000000000000 : ℝ)^6319
        have hw : |(-1027761479/5000000000 : ℝ)|=(1027761479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s3_7 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174326223/400000000 : ℝ)*x 0 + (56899547/125000000 : ℝ)*x 1 + (1043140199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174326223/400000000 : ℝ)^8367 ≤ (2081038287937/6250000000000 : ℝ)^6319 := by
    have hnat : (174326223 : ℕ)^8367*6250000000000^6319 ≤ 2081038287937^6319*400000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174326223 400000000 2081038287937 6250000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56899547/125000000 : ℝ)^8367 ≤ (35271211004941/100000000000000 : ℝ)^6319 := by
    have hnat : (56899547 : ℕ)^8367*100000000000000^6319 ≤ 35271211004941^6319*125000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56899547 125000000 35271211004941 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043140199/2500000000 : ℝ)^8367 ≤ (31432176376311/100000000000000 : ℝ)^6319 := by
    have hnat : (1043140199 : ℕ)^8367*100000000000000^6319 ≤ 31432176376311^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043140199 2500000000 31432176376311 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174326223/400000000 : ℝ), (56899547/125000000 : ℝ), (1043140199/2500000000 : ℝ)] ![(2081038287937/6250000000000 : ℝ), (35271211004941/100000000000000 : ℝ), (31432176376311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174326223/400000000 : ℝ)|^8367 ≤ (2081038287937/6250000000000 : ℝ)^6319
        have hw : |(174326223/400000000 : ℝ)|=(174326223/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56899547/125000000 : ℝ)|^8367 ≤ (35271211004941/100000000000000 : ℝ)^6319
        have hw : |(56899547/125000000 : ℝ)|=(56899547/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043140199/2500000000 : ℝ)|^8367 ≤ (31432176376311/100000000000000 : ℝ)^6319
        have hw : |(1043140199/2500000000 : ℝ)|=(1043140199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1174_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16409/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1341/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14769/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16409/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2303/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16409/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2303/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16409/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2303/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16409/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2303/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16409/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2303/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16409/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2303/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2303/25000 : ℝ) ^ (4183/1024 : ℝ) ≤ (5880662510489559/100000000000000000000 : ℝ) := by
    have hpowers : (2303/25000 : ℝ)^4183 ≤ (5880662510489559/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2303 : ℕ)^4183*100000000000000000000^1024 ≤ 5880662510489559^1024*25000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2303 25000 5880662510489559 100000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2303/25000 : ℝ)) (X := (5880662510489559/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16409/100000 : ℝ) ^ (4183/1024 : ℝ) ≤ (62178623100399687/100000000000000000000 : ℝ) := by
    have hpowers : (16409/100000 : ℝ)^4183 ≤ (62178623100399687/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16409 : ℕ)^4183*100000000000000000000^1024 ≤ 62178623100399687^1024*100000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16409 100000 62178623100399687 100000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16409/100000 : ℝ)) (X := (62178623100399687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005880662510489559/50000000000000000000 : ℝ) ≤ (2500071976225157/2500000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (50005880662510489559/50000000000000000000 : ℝ)^1024 ≤ (2500071976225157/2500000000000000 : ℝ)^4183 := by
      have hnat : (50005880662510489559 : ℕ)^1024*2500000000000000^4183 ≤ 2500071976225157^4183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005880662510489559 50000000000000000000 2500071976225157 2500000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500071976225157/2500000000000000 : ℝ)) (X := (50005880662510489559/50000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50034029642805444623/50000000000000000000 : ℝ) ≤ (250041641647827/250000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (50034029642805444623/50000000000000000000 : ℝ)^1024 ≤ (250041641647827/250000000000000 : ℝ)^4183 := by
      have hnat : (50034029642805444623 : ℕ)^1024*250000000000000^4183 ≤ 250041641647827^4183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034029642805444623 50000000000000000000 250041641647827 250000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250041641647827/250000000000000 : ℝ)) (X := (50034029642805444623/50000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50062178623100399687/50000000000000000000 : ℝ) ≤ (2500760856731383/2500000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (50062178623100399687/50000000000000000000 : ℝ)^1024 ≤ (2500760856731383/2500000000000000 : ℝ)^4183 := by
      have hnat : (50062178623100399687 : ℕ)^1024*2500000000000000^4183 ≤ 2500760856731383^4183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50062178623100399687 50000000000000000000 2500760856731383 2500000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500760856731383/2500000000000000 : ℝ)) (X := (50062178623100399687/50000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5880662510489559/100000000000000000000 : ℝ) ≤ ((17986672045669101017/17992500000000000000 : ℝ)+2*(344440253113/179925000000000 : ℝ)*(2303/25000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (17986672045669101017/17992500000000000000 : ℝ)+2*(344440253113/179925000000000 : ℝ)*(2303/25000 : ℝ)=(2500071976225157/2500000000000000 : ℝ) by norm_num, show 1+2*(5880662510489559/100000000000000000000 : ℝ)=(50005880662510489559/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(62178623100399687/100000000000000000000 : ℝ)+(5880662510489559/100000000000000000000 : ℝ) ≤ ((17986672045669101017/17992500000000000000 : ℝ)+(344440253113/179925000000000 : ℝ)*((16409/100000 : ℝ)+(2303/25000 : ℝ)))^(4183/1024 : ℝ) := by
    rw [show (17986672045669101017/17992500000000000000 : ℝ)+(344440253113/179925000000000 : ℝ)*((16409/100000 : ℝ)+(2303/25000 : ℝ))=(250041641647827/250000000000000 : ℝ) by norm_num, show 1+(62178623100399687/100000000000000000000 : ℝ)+(5880662510489559/100000000000000000000 : ℝ)=(50034029642805444623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(62178623100399687/100000000000000000000 : ℝ) ≤ ((17986672045669101017/17992500000000000000 : ℝ)+2*(344440253113/179925000000000 : ℝ)*(16409/100000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (17986672045669101017/17992500000000000000 : ℝ)+2*(344440253113/179925000000000 : ℝ)*(16409/100000 : ℝ)=(2500760856731383/2500000000000000 : ℝ) by norm_num, show 1+2*(62178623100399687/100000000000000000000 : ℝ)=(50062178623100399687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17986672045669101017/17992500000000000000 : ℝ)*(X 1 0+X 2 0)+(344440253113/179925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (2303/25000 : ℝ)) (hi := (16409/100000 : ℝ)) (c := (17986672045669101017/17992500000000000000 : ℝ)) (alpha := (344440253113/179925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17986672045669101017/17992500000000000000 : ℝ)*(X 0 1+X 2 1)+(344440253113/179925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (2303/25000 : ℝ)) (hi := (16409/100000 : ℝ)) (c := (17986672045669101017/17992500000000000000 : ℝ)) (alpha := (344440253113/179925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17986672045669101017/17992500000000000000 : ℝ)*(X 0 2+X 1 2)+(344440253113/179925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (2303/25000 : ℝ)) (hi := (16409/100000 : ℝ)) (c := (17986672045669101017/17992500000000000000 : ℝ)) (alpha := (344440253113/179925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-429642457/2000000000 : ℝ)*X 0 0+(5425965909/10000000000 : ℝ)*X 0 1+(209399903/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353035329/10000000000 : ℝ)*X 1 0+(-1122881139/5000000000 : ℝ)*X 1 1+(5234997377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070607083/2000000000 : ℝ)*X 2 0+(1046999473/2000000000 : ℝ)*X 2 1+(-112288109/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358122771/10000000000 : ℝ)*X 0 0+(4171101713/10000000000 : ℝ)*X 0 1+(4553414451/10000000000 : ℝ)*X 0 2+(4358122771/10000000000 : ℝ)*X 1 0+(4171101713/10000000000 : ℝ)*X 1 1+(4553414451/10000000000 : ℝ)*X 1 2+(4358122771/10000000000 : ℝ)*X 2 0+(4171101713/10000000000 : ℝ)*X 2 1+(4553414451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2148228811/10000000000 : ℝ)*X 0 0+(5235722367/10000000000 : ℝ)*X 0 1+(2712618607/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530454231/1000000000 : ℝ)*X 1 0+(-513880773/2500000000 : ℝ)*X 1 1+(5425237059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060908701/2000000000 : ℝ)*X 2 0+(5425235971/10000000000 : ℝ)*X 2 1+(-1027761479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174326223/400000000 : ℝ)*X 0 0+(56899547/125000000 : ℝ)*X 0 1+(1043140199/2500000000 : ℝ)*X 0 2+(174326223/400000000 : ℝ)*X 1 0+(56899547/125000000 : ℝ)*X 1 1+(1043140199/2500000000 : ℝ)*X 1 2+(174326223/400000000 : ℝ)*X 2 0+(56899547/125000000 : ℝ)*X 2 1+(1043140199/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105603874142052912750020451/37484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (835572171/100000000000000 : ℝ)*(base19) + (16834803/2000000000000 : ℝ)*(base23) + (20377/48828125000 : ℝ)*(lower2) + (20065649/50000000000000 : ℝ)*(upper3) + (103777409/100000000000000 : ℝ)*(upper5) + (31408660436101/800000000000 : ℝ)*(major0) + (31408660436101/800000000000 : ℝ)*(major1) + (1963041277256313/50000000000000 : ℝ)*(major2) + (2618240005608453/50000000000000 : ℝ)*(sp0) + (2618246272456899/50000000000000 : ℝ)*(sp1) + (5236492538745819/100000000000000 : ℝ)*(sp2) + (1307832879925577/50000000000000 : ℝ)*(sp3) + (6684634531/50000000000000 : ℝ)*(sp4) + (5874778879/100000000000000 : ℝ)*(sp7) + (163479477164377/6250000000000 : ℝ)*(f.failure) + (5236493380485969/100000000000000 : ℝ)*(f.sum) + (188737500909269/35985000000000000000000000000 : ℝ)*base66 + (95350865558694883/14394000000000000000000000000000 : ℝ)*base68 + (10050662781562720321/899625000000000000000000000000000 : ℝ)*base69 + (196394997421788883/14394000000000000000000000000000 : ℝ)*base72 + (7760430360587/4498125000000000000000000000 : ℝ)*base73 + (7917803378223220321/899625000000000000000000000000000 : ℝ)*base75 + (11994906300473761/4798000000000000000000000000000 : ℝ)*base78 + (55648601197407761/4798000000000000000000000000000 : ℝ)*base80 + (9781898528927/3598500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (498727/625000000000000000000 : ℝ)*base90 + (498727/625000000000000000000 : ℝ)*base92 + (6748727/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (454439307597359536396914711/74968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (281041853/50000000000000 : ℝ)*(base19) + (1858448771/100000000000000 : ℝ)*(base23) + (440471/5000000000000 : ℝ)*(upper2) + (67520283/100000000000000 : ℝ)*(upper3) + (9628961/25000000000000 : ℝ)*(upper5) + (989045477282589/25000000000000 : ℝ)*(major0) + (989045477282589/25000000000000 : ℝ)*(major1) + (989045477282589/25000000000000 : ℝ)*(major2) + (5668206749/100000000000000 : ℝ)*(sp1) + (1953460723/12500000000000 : ℝ)*(sp2) + (527663890652953/10000000000000 : ℝ)*(sp4) + (211065307049563/4000000000000 : ℝ)*(sp5) + (2638310710197487/50000000000000 : ℝ)*(sp6) + (82366397177311/3125000000000 : ℝ)*(sp7) + (82366397177311/3125000000000 : ℝ)*(f.failure) + (527663890652953/10000000000000 : ℝ)*(f.sum) + (117594903923/5997500000000000000000000000 : ℝ)*base66 + (2787478864698372671/149937500000000000000000000000000 : ℝ)*base67 + (1955379989784747671/149937500000000000000000000000000 : ℝ)*base69 + (1139245308800935171/149937500000000000000000000000000 : ℝ)*base71 + (37290301007647/5997500000000000000000000000 : ℝ)*base73 + (2255757523608372671/149937500000000000000000000000000 : ℝ)*base75 + (295938999048372671/149937500000000000000000000000000 : ℝ)*base77 + (734328989811122671/149937500000000000000000000000000 : ℝ)*base79 + (21025023930551/2998750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3409361/312500000000000000000 : ℝ)*base90 + (3409361/312500000000000000000 : ℝ)*base92 + (3409361/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1174_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16409/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1174_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1174_s4_0 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150965017/10000000000 : ℝ)*x 0 + (1350100239/2500000000 : ℝ)*x 1 + (1314690249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150965017/10000000000 : ℝ)^8367 ≤ (13071894587681/100000000000000 : ℝ)^6319 := by
    have hnat : (2150965017 : ℕ)^8367*100000000000000^6319 ≤ 13071894587681^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150965017 10000000000 13071894587681 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350100239/2500000000 : ℝ)^8367 ≤ (44228759780553/100000000000000 : ℝ)^6319 := by
    have hnat : (1350100239 : ℕ)^8367*100000000000000^6319 ≤ 44228759780553^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350100239 2500000000 44228759780553 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314690249/2500000000 : ℝ)^8367 ≤ (853986912307/2000000000000 : ℝ)^6319 := by
    have hnat : (1314690249 : ℕ)^8367*2000000000000^6319 ≤ 853986912307^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314690249 2500000000 853986912307 2000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150965017/10000000000 : ℝ), (1350100239/2500000000 : ℝ), (1314690249/2500000000 : ℝ)] ![(13071894587681/100000000000000 : ℝ), (44228759780553/100000000000000 : ℝ), (853986912307/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150965017/10000000000 : ℝ)|^8367 ≤ (13071894587681/100000000000000 : ℝ)^6319
        have hw : |(-2150965017/10000000000 : ℝ)|=(2150965017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350100239/2500000000 : ℝ)|^8367 ≤ (44228759780553/100000000000000 : ℝ)^6319
        have hw : |(1350100239/2500000000 : ℝ)|=(1350100239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314690249/2500000000 : ℝ)|^8367 ≤ (853986912307/2000000000000 : ℝ)^6319
        have hw : |(1314690249/2500000000 : ℝ)|=(1314690249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s4_1 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069326359/2000000000 : ℝ)*x 0 + (-444584337/2000000000 : ℝ)*x 1 + (2629380643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069326359/2000000000 : ℝ)^8367 ≤ (21823307797011/50000000000000 : ℝ)^6319 := by
    have hnat : (1069326359 : ℕ)^8367*50000000000000^6319 ≤ 21823307797011^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069326359 2000000000 21823307797011 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444584337/2000000000 : ℝ)^8367 ≤ (13654035667669/100000000000000 : ℝ)^6319 := by
    have hnat : (444584337 : ℕ)^8367*100000000000000^6319 ≤ 13654035667669^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444584337 2000000000 13654035667669 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629380643/5000000000 : ℝ)^8367 ≤ (21349674366607/50000000000000 : ℝ)^6319 := by
    have hnat : (2629380643 : ℕ)^8367*50000000000000^6319 ≤ 21349674366607^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629380643 5000000000 21349674366607 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069326359/2000000000 : ℝ), (-444584337/2000000000 : ℝ), (2629380643/5000000000 : ℝ)] ![(21823307797011/50000000000000 : ℝ), (13654035667669/100000000000000 : ℝ), (21349674366607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069326359/2000000000 : ℝ)|^8367 ≤ (21823307797011/50000000000000 : ℝ)^6319
        have hw : |(1069326359/2000000000 : ℝ)|=(1069326359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-444584337/2000000000 : ℝ)|^8367 ≤ (13654035667669/100000000000000 : ℝ)^6319
        have hw : |(-444584337/2000000000 : ℝ)|=(444584337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629380643/5000000000 : ℝ)|^8367 ≤ (21349674366607/50000000000000 : ℝ)^6319
        have hw : |(2629380643/5000000000 : ℝ)|=(2629380643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s4_2 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336657917/2500000000 : ℝ)*x 0 + (21035047/40000000 : ℝ)*x 1 + (-2222921239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336657917/2500000000 : ℝ)^8367 ≤ (43646614221259/100000000000000 : ℝ)^6319 := by
    have hnat : (1336657917 : ℕ)^8367*100000000000000^6319 ≤ 43646614221259^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336657917 2500000000 43646614221259 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21035047/40000000 : ℝ)^8367 ≤ (42699353721797/100000000000000 : ℝ)^6319 := by
    have hnat : (21035047 : ℕ)^8367*100000000000000^6319 ≤ 42699353721797^6319*40000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21035047 40000000 42699353721797 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2222921239/10000000000 : ℝ)^8367 ≤ (426688501259/3125000000000 : ℝ)^6319 := by
    have hnat : (2222921239 : ℕ)^8367*3125000000000^6319 ≤ 426688501259^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222921239 10000000000 426688501259 3125000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336657917/2500000000 : ℝ), (21035047/40000000 : ℝ), (-2222921239/10000000000 : ℝ)] ![(43646614221259/100000000000000 : ℝ), (42699353721797/100000000000000 : ℝ), (426688501259/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336657917/2500000000 : ℝ)|^8367 ≤ (43646614221259/100000000000000 : ℝ)^6319
        have hw : |(1336657917/2500000000 : ℝ)|=(1336657917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21035047/40000000 : ℝ)|^8367 ≤ (42699353721797/100000000000000 : ℝ)^6319
        have hw : |(21035047/40000000 : ℝ)|=(21035047/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2222921239/10000000000 : ℝ)|^8367 ≤ (426688501259/3125000000000 : ℝ)^6319
        have hw : |(-2222921239/10000000000 : ℝ)|=(2222921239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s4_3 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (68121407/156250000 : ℝ)*x 0 + (42202663/100000000 : ℝ)*x 1 + (4503824681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68121407/156250000 : ℝ)^8367 ≤ (33312945969173/100000000000000 : ℝ)^6319 := by
    have hnat : (68121407 : ℕ)^8367*100000000000000^6319 ≤ 33312945969173^6319*156250000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68121407 156250000 33312945969173 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42202663/100000000 : ℝ)^8367 ≤ (7977224134123/25000000000000 : ℝ)^6319 := by
    have hnat : (42202663 : ℕ)^8367*25000000000000^6319 ≤ 7977224134123^6319*100000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42202663 100000000 7977224134123 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503824681/10000000000 : ℝ)^8367 ≤ (4347269685341/12500000000000 : ℝ)^6319 := by
    have hnat : (4503824681 : ℕ)^8367*12500000000000^6319 ≤ 4347269685341^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503824681 10000000000 4347269685341 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68121407/156250000 : ℝ), (42202663/100000000 : ℝ), (4503824681/10000000000 : ℝ)] ![(33312945969173/100000000000000 : ℝ), (7977224134123/25000000000000 : ℝ), (4347269685341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68121407/156250000 : ℝ)|^8367 ≤ (33312945969173/100000000000000 : ℝ)^6319
        have hw : |(68121407/156250000 : ℝ)|=(68121407/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42202663/100000000 : ℝ)|^8367 ≤ (7977224134123/25000000000000 : ℝ)^6319
        have hw : |(42202663/100000000 : ℝ)|=(42202663/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503824681/10000000000 : ℝ)|^8367 ≤ (4347269685341/12500000000000 : ℝ)^6319
        have hw : |(4503824681/10000000000 : ℝ)|=(4503824681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s4_4 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150971721/10000000000 : ℝ)*x 0 + (657395099/1250000000 : ℝ)*x 1 + (1079999921/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150971721/10000000000 : ℝ)^8367 ≤ (13071948533877/100000000000000 : ℝ)^6319 := by
    have hnat : (2150971721 : ℕ)^8367*100000000000000^6319 ≤ 13071948533877^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150971721 10000000000 13071948533877 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657395099/1250000000 : ℝ)^8367 ≤ (8540728795483/20000000000000 : ℝ)^6319 := by
    have hnat : (657395099 : ℕ)^8367*20000000000000^6319 ≤ 8540728795483^6319*1250000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657395099 1250000000 8540728795483 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079999921/2000000000 : ℝ)^8367 ≤ (4422440747589/10000000000000 : ℝ)^6319 := by
    have hnat : (1079999921 : ℕ)^8367*10000000000000^6319 ≤ 4422440747589^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079999921 2000000000 4422440747589 10000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150971721/10000000000 : ℝ), (657395099/1250000000 : ℝ), (1079999921/2000000000 : ℝ)] ![(13071948533877/100000000000000 : ℝ), (8540728795483/20000000000000 : ℝ), (4422440747589/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150971721/10000000000 : ℝ)|^8367 ≤ (13071948533877/100000000000000 : ℝ)^6319
        have hw : |(-2150971721/10000000000 : ℝ)|=(2150971721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657395099/1250000000 : ℝ)|^8367 ≤ (8540728795483/20000000000000 : ℝ)^6319
        have hw : |(657395099/1250000000 : ℝ)|=(657395099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079999921/2000000000 : ℝ)|^8367 ≤ (4422440747589/10000000000000 : ℝ)^6319
        have hw : |(1079999921/2000000000 : ℝ)|=(1079999921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s4_5 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106213299/200000000 : ℝ)*x 0 + (-41633659/200000000 : ℝ)*x 1 + (1079999939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106213299/200000000 : ℝ)^8367 ≤ (10814567218167/25000000000000 : ℝ)^6319 := by
    have hnat : (106213299 : ℕ)^8367*25000000000000^6319 ≤ 10814567218167^6319*200000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106213299 200000000 10814567218167 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41633659/200000000 : ℝ)^8367 ≤ (12517322654969/100000000000000 : ℝ)^6319 := by
    have hnat : (41633659 : ℕ)^8367*100000000000000^6319 ≤ 12517322654969^6319*200000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41633659 200000000 12517322654969 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079999939/2000000000 : ℝ)^8367 ≤ (884488169037/2000000000000 : ℝ)^6319 := by
    have hnat : (1079999939 : ℕ)^8367*2000000000000^6319 ≤ 884488169037^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079999939 2000000000 884488169037 2000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106213299/200000000 : ℝ), (-41633659/200000000 : ℝ), (1079999939/2000000000 : ℝ)] ![(10814567218167/25000000000000 : ℝ), (12517322654969/100000000000000 : ℝ), (884488169037/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106213299/200000000 : ℝ)|^8367 ≤ (10814567218167/25000000000000 : ℝ)^6319
        have hw : |(106213299/200000000 : ℝ)|=(106213299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41633659/200000000 : ℝ)|^8367 ≤ (12517322654969/100000000000000 : ℝ)^6319
        have hw : |(-41633659/200000000 : ℝ)|=(41633659/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079999939/2000000000 : ℝ)|^8367 ≤ (884488169037/2000000000000 : ℝ)^6319
        have hw : |(1079999939/2000000000 : ℝ)|=(1079999939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s4_6 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310665071/10000000000 : ℝ)*x 0 + (2699999763/5000000000 : ℝ)*x 1 + (-2081683017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310665071/10000000000 : ℝ)^8367 ≤ (21629135088859/50000000000000 : ℝ)^6319 := by
    have hnat : (5310665071 : ℕ)^8367*50000000000000^6319 ≤ 21629135088859^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310665071 10000000000 21629135088859 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699999763/5000000000 : ℝ)^8367 ≤ (44224406619213/100000000000000 : ℝ)^6319 := by
    have hnat : (2699999763 : ℕ)^8367*100000000000000^6319 ≤ 44224406619213^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699999763 5000000000 44224406619213 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081683017/10000000000 : ℝ)^8367 ≤ (12517323188419/100000000000000 : ℝ)^6319 := by
    have hnat : (2081683017 : ℕ)^8367*100000000000000^6319 ≤ 12517323188419^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081683017 10000000000 12517323188419 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310665071/10000000000 : ℝ), (2699999763/5000000000 : ℝ), (-2081683017/10000000000 : ℝ)] ![(21629135088859/50000000000000 : ℝ), (44224406619213/100000000000000 : ℝ), (12517323188419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310665071/10000000000 : ℝ)|^8367 ≤ (21629135088859/50000000000000 : ℝ)^6319
        have hw : |(5310665071/10000000000 : ℝ)|=(5310665071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699999763/5000000000 : ℝ)|^8367 ≤ (44224406619213/100000000000000 : ℝ)^6319
        have hw : |(2699999763/5000000000 : ℝ)|=(2699999763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2081683017/10000000000 : ℝ)|^8367 ≤ (12517323188419/100000000000000 : ℝ)^6319
        have hw : |(-2081683017/10000000000 : ℝ)|=(2081683017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s4_7 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179891483/5000000000 : ℝ)*x 0 + (4503024701/10000000000 : ℝ)*x 1 + (4221070217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179891483/5000000000 : ℝ)^8367 ≤ (8328269166599/25000000000000 : ℝ)^6319 := by
    have hnat : (2179891483 : ℕ)^8367*25000000000000^6319 ≤ 8328269166599^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179891483 5000000000 8328269166599 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503024701/10000000000 : ℝ)^8367 ≤ (34769978239277/100000000000000 : ℝ)^6319 := by
    have hnat : (4503024701 : ℕ)^8367*100000000000000^6319 ≤ 34769978239277^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503024701 10000000000 34769978239277 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4221070217/10000000000 : ℝ)^8367 ≤ (31916945092333/100000000000000 : ℝ)^6319 := by
    have hnat : (4221070217 : ℕ)^8367*100000000000000^6319 ≤ 31916945092333^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221070217 10000000000 31916945092333 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179891483/5000000000 : ℝ), (4503024701/10000000000 : ℝ), (4221070217/10000000000 : ℝ)] ![(8328269166599/25000000000000 : ℝ), (34769978239277/100000000000000 : ℝ), (31916945092333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179891483/5000000000 : ℝ)|^8367 ≤ (8328269166599/25000000000000 : ℝ)^6319
        have hw : |(2179891483/5000000000 : ℝ)|=(2179891483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503024701/10000000000 : ℝ)|^8367 ≤ (34769978239277/100000000000000 : ℝ)^6319
        have hw : |(4503024701/10000000000 : ℝ)|=(4503024701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4221070217/10000000000 : ℝ)|^8367 ≤ (31916945092333/100000000000000 : ℝ)^6319
        have hw : |(4221070217/10000000000 : ℝ)|=(4221070217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1174_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2247/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1341/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1341/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1341/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1341/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1341/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1341/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1341/12500 : ℝ) ^ (4183/1024 : ℝ) ≤ (438295504358887/4000000000000000000 : ℝ) := by
    have hpowers : (1341/12500 : ℝ)^4183 ≤ (438295504358887/4000000000000000000 : ℝ)^1024 := by
      have hnat : (1341 : ℕ)^4183*4000000000000000000^1024 ≤ 438295504358887^1024*12500^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1341 12500 438295504358887 4000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1341/12500 : ℝ)) (X := (438295504358887/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14769/100000 : ℝ) ^ (4183/1024 : ℝ) ≤ (40441909396547731/100000000000000000000 : ℝ) := by
    have hpowers : (14769/100000 : ℝ)^4183 ≤ (40441909396547731/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14769 : ℕ)^4183*100000000000000000000^1024 ≤ 40441909396547731^1024*100000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14769 100000 40441909396547731 100000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14769/100000 : ℝ)) (X := (40441909396547731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000438295504358887/2000000000000000000 : ℝ) ≤ (125006705376849/125000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (2000438295504358887/2000000000000000000 : ℝ)^1024 ≤ (125006705376849/125000000000000 : ℝ)^4183 := by
      have hnat : (2000438295504358887 : ℕ)^1024*125000000000000^4183 ≤ 125006705376849^4183*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000438295504358887 2000000000000000000 125006705376849 125000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125006705376849/125000000000000 : ℝ)) (X := (2000438295504358887/2000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025699648502759953/50000000000000000000 : ℝ) ≤ (10001258012623073/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (50025699648502759953/50000000000000000000 : ℝ)^1024 ≤ (10001258012623073/10000000000000000 : ℝ)^4183 := by
      have hnat : (50025699648502759953 : ℕ)^1024*10000000000000000^4183 ≤ 10001258012623073^4183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025699648502759953 50000000000000000000 10001258012623073 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001258012623073/10000000000000000 : ℝ)) (X := (50025699648502759953/50000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040441909396547731/50000000000000000000 : ℝ) ≤ (5000989797549113/5000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (50040441909396547731/50000000000000000000 : ℝ)^1024 ≤ (5000989797549113/5000000000000000 : ℝ)^4183 := by
      have hnat : (50040441909396547731 : ℕ)^1024*5000000000000000^4183 ≤ 5000989797549113^4183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040441909396547731 50000000000000000000 5000989797549113 5000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000989797549113/5000000000000000 : ℝ)) (X := (50040441909396547731/50000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(438295504358887/4000000000000000000 : ℝ) ≤ ((17533283611389263/17539062500000000 : ℝ)+2*(721582475153/404100000000000 : ℝ)*(1341/12500 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (17533283611389263/17539062500000000 : ℝ)+2*(721582475153/404100000000000 : ℝ)*(1341/12500 : ℝ)=(125006705376849/125000000000000 : ℝ) by norm_num, show 1+2*(438295504358887/4000000000000000000 : ℝ)=(2000438295504358887/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40441909396547731/100000000000000000000 : ℝ)+(438295504358887/4000000000000000000 : ℝ) ≤ ((17533283611389263/17539062500000000 : ℝ)+(721582475153/404100000000000 : ℝ)*((14769/100000 : ℝ)+(1341/12500 : ℝ)))^(4183/1024 : ℝ) := by
    rw [show (17533283611389263/17539062500000000 : ℝ)+(721582475153/404100000000000 : ℝ)*((14769/100000 : ℝ)+(1341/12500 : ℝ))=(10001258012623073/10000000000000000 : ℝ) by norm_num, show 1+(40441909396547731/100000000000000000000 : ℝ)+(438295504358887/4000000000000000000 : ℝ)=(50025699648502759953/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40441909396547731/100000000000000000000 : ℝ) ≤ ((17533283611389263/17539062500000000 : ℝ)+2*(721582475153/404100000000000 : ℝ)*(14769/100000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (17533283611389263/17539062500000000 : ℝ)+2*(721582475153/404100000000000 : ℝ)*(14769/100000 : ℝ)=(5000989797549113/5000000000000000 : ℝ) by norm_num, show 1+2*(40441909396547731/100000000000000000000 : ℝ)=(50040441909396547731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17533283611389263/17539062500000000 : ℝ)*(X 1 0+X 2 0)+(721582475153/404100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (1341/12500 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (17533283611389263/17539062500000000 : ℝ)) (alpha := (721582475153/404100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17533283611389263/17539062500000000 : ℝ)*(X 0 1+X 2 1)+(721582475153/404100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (1341/12500 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (17533283611389263/17539062500000000 : ℝ)) (alpha := (721582475153/404100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17533283611389263/17539062500000000 : ℝ)*(X 0 2+X 1 2)+(721582475153/404100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (1341/12500 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (17533283611389263/17539062500000000 : ℝ)) (alpha := (721582475153/404100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2150965017/10000000000 : ℝ)*X 0 0+(1350100239/2500000000 : ℝ)*X 0 1+(1314690249/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069326359/2000000000 : ℝ)*X 1 0+(-444584337/2000000000 : ℝ)*X 1 1+(2629380643/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336657917/2500000000 : ℝ)*X 2 0+(21035047/40000000 : ℝ)*X 2 1+(-2222921239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((68121407/156250000 : ℝ)*X 0 0+(42202663/100000000 : ℝ)*X 0 1+(4503824681/10000000000 : ℝ)*X 0 2+(68121407/156250000 : ℝ)*X 1 0+(42202663/100000000 : ℝ)*X 1 1+(4503824681/10000000000 : ℝ)*X 1 2+(68121407/156250000 : ℝ)*X 2 0+(42202663/100000000 : ℝ)*X 2 1+(4503824681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2150971721/10000000000 : ℝ)*X 0 0+(657395099/1250000000 : ℝ)*X 0 1+(1079999921/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106213299/200000000 : ℝ)*X 1 0+(-41633659/200000000 : ℝ)*X 1 1+(1079999939/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310665071/10000000000 : ℝ)*X 2 0+(2699999763/5000000000 : ℝ)*X 2 1+(-2081683017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179891483/5000000000 : ℝ)*X 0 0+(4503024701/10000000000 : ℝ)*X 0 1+(4221070217/10000000000 : ℝ)*X 0 2+(2179891483/5000000000 : ℝ)*X 1 0+(4503024701/10000000000 : ℝ)*X 1 1+(4221070217/10000000000 : ℝ)*X 1 2+(2179891483/5000000000 : ℝ)*X 2 0+(4503024701/10000000000 : ℝ)*X 2 1+(4221070217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3226059814618770601373/1122500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1128062249/100000000000000 : ℝ)*(base19) + (906452897/100000000000000 : ℝ)*(base23) + (38391429/100000000000000 : ℝ)*(lower2) + (489383181/100000000000000 : ℝ)*(upper5) + (330840384387429/6250000000000 : ℝ)*(major0) + (330840384387429/6250000000000 : ℝ)*(major1) + (330840384387429/6250000000000 : ℝ)*(major2) + (3530093856639987/50000000000000 : ℝ)*(sp0) + (441264934354321/6250000000000 : ℝ)*(sp1) + (7060241832100949/100000000000000 : ℝ)*(sp2) + (705326922613053/20000000000000 : ℝ)*(sp3) + (3439079617/6250000000000 : ℝ)*(sp4) + (1330411231/50000000000000 : ℝ)*(sp5) + (371324469/2500000000000 : ℝ)*(sp7) + (141065978641761/4000000000000 : ℝ)*(f.failure) + (3530121369276923/50000000000000 : ℝ)*(f.sum) + (15301312099357/3367500000000000000000000000 : ℝ)*base65 + (54275420412294821/5261718750000000000000000000000 : ℝ)*base67 + (223790550402180091/21046875000000000000000000000000 : ℝ)*base70 + (33657013105326071/5261718750000000000000000000000 : ℝ)*base71 + (16238880629/420937500000000000000000000 : ℝ)*base73 + (136216678132398841/21046875000000000000000000000000 : ℝ)*base76 + (94101707517576071/5261718750000000000000000000000 : ℝ)*base77 + (2684197993800983/10523437500000000000000000000000 : ℝ)*base80 + (8086308661913/3367500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3271311/400000000000000000000 : ℝ)*base90 + (3271311/400000000000000000000 : ℝ)*base92 + (3271311/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11086385771738974432484847/7015625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (976562659/100000000000000 : ℝ)*(base19) + (709581539/50000000000000 : ℝ)*(base23) + (2331771/1562500000000 : ℝ)*(upper2) + (31350753/25000000000000 : ℝ)*(upper5) + (2661747493784097/50000000000000 : ℝ)*(major0) + (2661747493784097/50000000000000 : ℝ)*(major1) + (2661747493784097/50000000000000 : ℝ)*(major2) + (659529081/50000000000000 : ℝ)*(sp0) + (37649244189/100000000000000 : ℝ)*(sp1) + (37622545943/100000000000000 : ℝ)*(sp2) + (3550159859195879/50000000000000 : ℝ)*(sp4) + (110941912681923/1562500000000 : ℝ)*(sp5) + (7100281995740897/100000000000000 : ℝ)*(sp6) + (1773334442505863/50000000000000 : ℝ)*(sp7) + (1773334442505863/50000000000000 : ℝ)*(f.failure) + (7100321037449919/100000000000000 : ℝ)*(f.sum) + (5668657021723/3367500000000000000000000000 : ℝ)*base66 + (168322452272990389/21046875000000000000000000000000 : ℝ)*base67 + (64037915375334139/21046875000000000000000000000000 : ℝ)*base69 + (16644632085684493/10523437500000000000000000000000 : ℝ)*base72 + (15743999612059/6735000000000000000000000000 : ℝ)*base73 + (216016542120665861/21046875000000000000000000000000 : ℝ)*base76 + (98211153908596757/10523437500000000000000000000000 : ℝ)*base77 + (32971264822865389/21046875000000000000000000000000 : ℝ)*base79 + (12174228815683/3367500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (9706487/5000000000000000000000 : ℝ)*base89 + (9706487/5000000000000000000000 : ℝ)*base91 + (9706487/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1174_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1174_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1174_s5_0 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1075767779/5000000000 : ℝ)*x 0 + (539408497/1000000000 : ℝ)*x 1 + (5264702283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075767779/5000000000 : ℝ)^8367 ≤ (1634560731279/12500000000000 : ℝ)^6319 := by
    have hnat : (1075767779 : ℕ)^8367*12500000000000^6319 ≤ 1634560731279^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075767779 5000000000 1634560731279 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539408497/1000000000 : ℝ)^8367 ≤ (11040070132879/25000000000000 : ℝ)^6319 := by
    have hnat : (539408497 : ℕ)^8367*25000000000000^6319 ≤ 11040070132879^6319*1000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539408497 1000000000 11040070132879 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264702283/10000000000 : ℝ)^8367 ≤ (42763233604091/100000000000000 : ℝ)^6319 := by
    have hnat : (5264702283 : ℕ)^8367*100000000000000^6319 ≤ 42763233604091^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264702283 10000000000 42763233604091 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1075767779/5000000000 : ℝ), (539408497/1000000000 : ℝ), (5264702283/10000000000 : ℝ)] ![(1634560731279/12500000000000 : ℝ), (11040070132879/25000000000000 : ℝ), (42763233604091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1075767779/5000000000 : ℝ)|^8367 ≤ (1634560731279/12500000000000 : ℝ)^6319
        have hw : |(-1075767779/5000000000 : ℝ)|=(1075767779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539408497/1000000000 : ℝ)|^8367 ≤ (11040070132879/25000000000000 : ℝ)^6319
        have hw : |(539408497/1000000000 : ℝ)|=(539408497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264702283/10000000000 : ℝ)|^8367 ≤ (42763233604091/100000000000000 : ℝ)^6319
        have hw : |(5264702283/10000000000 : ℝ)|=(5264702283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s5_1 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672521489/5000000000 : ℝ)*x 0 + (-277146977/1250000000 : ℝ)*x 1 + (1316175581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672521489/5000000000 : ℝ)^8367 ≤ (4362944265321/10000000000000 : ℝ)^6319 := by
    have hnat : (2672521489 : ℕ)^8367*10000000000000^6319 ≤ 4362944265321^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672521489 5000000000 4362944265321 10000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277146977/1250000000 : ℝ)^8367 ≤ (13607323292997/100000000000000 : ℝ)^6319 := by
    have hnat : (277146977 : ℕ)^8367*100000000000000^6319 ≤ 13607323292997^6319*1250000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277146977 1250000000 13607323292997 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316175581/2500000000 : ℝ)^8367 ≤ (42763234045053/100000000000000 : ℝ)^6319 := by
    have hnat : (1316175581 : ℕ)^8367*100000000000000^6319 ≤ 42763234045053^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316175581 2500000000 42763234045053 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672521489/5000000000 : ℝ), (-277146977/1250000000 : ℝ), (1316175581/2500000000 : ℝ)] ![(4362944265321/10000000000000 : ℝ), (13607323292997/100000000000000 : ℝ), (42763234045053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672521489/5000000000 : ℝ)|^8367 ≤ (4362944265321/10000000000000 : ℝ)^6319
        have hw : |(2672521489/5000000000 : ℝ)|=(2672521489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277146977/1250000000 : ℝ)|^8367 ≤ (13607323292997/100000000000000 : ℝ)^6319
        have hw : |(-277146977/1250000000 : ℝ)|=(277146977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316175581/2500000000 : ℝ)|^8367 ≤ (42763234045053/100000000000000 : ℝ)^6319
        have hw : |(1316175581/2500000000 : ℝ)|=(1316175581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s5_2 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069008599/2000000000 : ℝ)*x 0 + (5264702223/10000000000 : ℝ)*x 1 + (-88687037/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069008599/2000000000 : ℝ)^8367 ≤ (43629442836947/100000000000000 : ℝ)^6319 := by
    have hnat : (1069008599 : ℕ)^8367*100000000000000^6319 ≤ 43629442836947^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069008599 2000000000 43629442836947 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264702223/10000000000 : ℝ)^8367 ≤ (42763232958779/100000000000000 : ℝ)^6319 := by
    have hnat : (5264702223 : ℕ)^8367*100000000000000^6319 ≤ 42763232958779^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264702223 10000000000 42763232958779 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88687037/400000000 : ℝ)^8367 ≤ (6803662089383/50000000000000 : ℝ)^6319 := by
    have hnat : (88687037 : ℕ)^8367*50000000000000^6319 ≤ 6803662089383^6319*400000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88687037 400000000 6803662089383 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069008599/2000000000 : ℝ), (5264702223/10000000000 : ℝ), (-88687037/400000000 : ℝ)] ![(43629442836947/100000000000000 : ℝ), (42763232958779/100000000000000 : ℝ), (6803662089383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069008599/2000000000 : ℝ)|^8367 ≤ (43629442836947/100000000000000 : ℝ)^6319
        have hw : |(1069008599/2000000000 : ℝ)|=(1069008599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264702223/10000000000 : ℝ)|^8367 ≤ (42763232958779/100000000000000 : ℝ)^6319
        have hw : |(5264702223/10000000000 : ℝ)|=(5264702223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88687037/400000000 : ℝ)|^8367 ≤ (6803662089383/50000000000000 : ℝ)^6319
        have hw : |(-88687037/400000000 : ℝ)|=(88687037/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s5_3 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360103239/10000000000 : ℝ)*x 0 + (423249227/1000000000 : ℝ)*x 1 + (280719557/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360103239/10000000000 : ℝ)^8367 ≤ (33316317052681/100000000000000 : ℝ)^6319 := by
    have hnat : (4360103239 : ℕ)^8367*100000000000000^6319 ≤ 33316317052681^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360103239 10000000000 33316317052681 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423249227/1000000000 : ℝ)^8367 ≤ (16015676310773/50000000000000 : ℝ)^6319 := by
    have hnat : (423249227 : ℕ)^8367*50000000000000^6319 ≤ 16015676310773^6319*1000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423249227 1000000000 16015676310773 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280719557/625000000 : ℝ)^8367 ≤ (3465233031609/10000000000000 : ℝ)^6319 := by
    have hnat : (280719557 : ℕ)^8367*10000000000000^6319 ≤ 3465233031609^6319*625000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280719557 625000000 3465233031609 10000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360103239/10000000000 : ℝ), (423249227/1000000000 : ℝ), (280719557/625000000 : ℝ)] ![(33316317052681/100000000000000 : ℝ), (16015676310773/50000000000000 : ℝ), (3465233031609/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360103239/10000000000 : ℝ)|^8367 ≤ (33316317052681/100000000000000 : ℝ)^6319
        have hw : |(4360103239/10000000000 : ℝ)|=(4360103239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423249227/1000000000 : ℝ)|^8367 ≤ (16015676310773/50000000000000 : ℝ)^6319
        have hw : |(423249227/1000000000 : ℝ)|=(423249227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280719557/625000000 : ℝ)|^8367 ≤ (3465233031609/10000000000000 : ℝ)^6319
        have hw : |(280719557/625000000 : ℝ)|=(280719557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s5_4 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151541187/10000000000 : ℝ)*x 0 + (5265035249/10000000000 : ℝ)*x 1 + (1348437607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151541187/10000000000 : ℝ)^8367 ≤ (13076531149937/100000000000000 : ℝ)^6319 := by
    have hnat : (2151541187 : ℕ)^8367*100000000000000^6319 ≤ 13076531149937^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151541187 10000000000 13076531149937 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265035249/10000000000 : ℝ)^8367 ≤ (1710672590151/4000000000000 : ℝ)^6319 := by
    have hnat : (5265035249 : ℕ)^8367*4000000000000^6319 ≤ 1710672590151^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265035249 10000000000 1710672590151 4000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348437607/2500000000 : ℝ)^8367 ≤ (44156654081149/100000000000000 : ℝ)^6319 := by
    have hnat : (1348437607 : ℕ)^8367*100000000000000^6319 ≤ 44156654081149^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348437607 2500000000 44156654081149 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151541187/10000000000 : ℝ), (5265035249/10000000000 : ℝ), (1348437607/2500000000 : ℝ)] ![(13076531149937/100000000000000 : ℝ), (1710672590151/4000000000000 : ℝ), (44156654081149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151541187/10000000000 : ℝ)|^8367 ≤ (13076531149937/100000000000000 : ℝ)^6319
        have hw : |(-2151541187/10000000000 : ℝ)|=(2151541187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265035249/10000000000 : ℝ)|^8367 ≤ (1710672590151/4000000000000 : ℝ)^6319
        have hw : |(5265035249/10000000000 : ℝ)|=(5265035249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348437607/2500000000 : ℝ)|^8367 ≤ (44156654081149/100000000000000 : ℝ)^6319
        have hw : |(1348437607/2500000000 : ℝ)|=(1348437607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s5_5 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656093327/5000000000 : ℝ)*x 0 + (-1044064107/5000000000 : ℝ)*x 1 + (5393750313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656093327/5000000000 : ℝ)^8367 ≤ (21637341012363/50000000000000 : ℝ)^6319 := by
    have hnat : (2656093327 : ℕ)^8367*50000000000000^6319 ≤ 21637341012363^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656093327 5000000000 21637341012363 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044064107/5000000000 : ℝ)^8367 ≤ (3142166279009/25000000000000 : ℝ)^6319 := by
    have hnat : (1044064107 : ℕ)^8367*25000000000000^6319 ≤ 3142166279009^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044064107 5000000000 3142166279009 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393750313/10000000000 : ℝ)^8367 ≤ (11039163208639/25000000000000 : ℝ)^6319 := by
    have hnat : (5393750313 : ℕ)^8367*25000000000000^6319 ≤ 11039163208639^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393750313 10000000000 11039163208639 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656093327/5000000000 : ℝ), (-1044064107/5000000000 : ℝ), (5393750313/10000000000 : ℝ)] ![(21637341012363/50000000000000 : ℝ), (3142166279009/25000000000000 : ℝ), (11039163208639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656093327/5000000000 : ℝ)|^8367 ≤ (21637341012363/50000000000000 : ℝ)^6319
        have hw : |(2656093327/5000000000 : ℝ)|=(2656093327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1044064107/5000000000 : ℝ)|^8367 ≤ (3142166279009/25000000000000 : ℝ)^6319
        have hw : |(-1044064107/5000000000 : ℝ)|=(1044064107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393750313/10000000000 : ℝ)|^8367 ≤ (11039163208639/25000000000000 : ℝ)^6319
        have hw : |(5393750313/10000000000 : ℝ)|=(5393750313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s5_6 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656093599/5000000000 : ℝ)*x 0 + (5393749759/10000000000 : ℝ)*x 1 + (-2088128233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656093599/5000000000 : ℝ)^8367 ≤ (43274687892601/100000000000000 : ℝ)^6319 := by
    have hnat : (2656093599 : ℕ)^8367*100000000000000^6319 ≤ 43274687892601^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656093599 5000000000 43274687892601 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393749759/10000000000 : ℝ)^8367 ≤ (2759790426827/6250000000000 : ℝ)^6319 := by
    have hnat : (5393749759 : ℕ)^8367*6250000000000^6319 ≤ 2759790426827^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393749759 10000000000 2759790426827 6250000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088128233/10000000000 : ℝ)^8367 ≤ (2513733053493/20000000000000 : ℝ)^6319 := by
    have hnat : (2088128233 : ℕ)^8367*20000000000000^6319 ≤ 2513733053493^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088128233 10000000000 2513733053493 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656093599/5000000000 : ℝ), (5393749759/10000000000 : ℝ), (-2088128233/10000000000 : ℝ)] ![(43274687892601/100000000000000 : ℝ), (2759790426827/6250000000000 : ℝ), (2513733053493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656093599/5000000000 : ℝ)|^8367 ≤ (43274687892601/100000000000000 : ℝ)^6319
        have hw : |(2656093599/5000000000 : ℝ)|=(2656093599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393749759/10000000000 : ℝ)|^8367 ≤ (2759790426827/6250000000000 : ℝ)^6319
        have hw : |(5393749759/10000000000 : ℝ)|=(5393749759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088128233/10000000000 : ℝ)|^8367 ≤ (2513733053493/20000000000000 : ℝ)^6319
        have hw : |(-2088128233/10000000000 : ℝ)|=(2088128233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s5_7 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360113369/10000000000 : ℝ)*x 0 + (4490845229/10000000000 : ℝ)*x 1 + (4233162669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360113369/10000000000 : ℝ)^8367 ≤ (33316419544981/100000000000000 : ℝ)^6319 := by
    have hnat : (4360113369 : ℕ)^8367*100000000000000^6319 ≤ 33316419544981^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360113369 10000000000 33316419544981 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490845229/10000000000 : ℝ)^8367 ≤ (17322754869963/50000000000000 : ℝ)^6319 := by
    have hnat : (4490845229 : ℕ)^8367*50000000000000^6319 ≤ 17322754869963^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490845229 10000000000 17322754869963 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233162669/10000000000 : ℝ)^8367 ≤ (6407614139851/20000000000000 : ℝ)^6319 := by
    have hnat : (4233162669 : ℕ)^8367*20000000000000^6319 ≤ 6407614139851^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233162669 10000000000 6407614139851 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360113369/10000000000 : ℝ), (4490845229/10000000000 : ℝ), (4233162669/10000000000 : ℝ)] ![(33316419544981/100000000000000 : ℝ), (17322754869963/50000000000000 : ℝ), (6407614139851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360113369/10000000000 : ℝ)|^8367 ≤ (33316419544981/100000000000000 : ℝ)^6319
        have hw : |(4360113369/10000000000 : ℝ)|=(4360113369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490845229/10000000000 : ℝ)|^8367 ≤ (17322754869963/50000000000000 : ℝ)^6319
        have hw : |(4490845229/10000000000 : ℝ)|=(4490845229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233162669/10000000000 : ℝ)|^8367 ≤ (6407614139851/20000000000000 : ℝ)^6319
        have hw : |(4233162669/10000000000 : ℝ)|=(4233162669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1174_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11361/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7051/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2247/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2247/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2247/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2247/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2247/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2247/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2247/20000 : ℝ) ^ (4183/1024 : ℝ) ≤ (2646415924506733/20000000000000000000 : ℝ) := by
    have hpowers : (2247/20000 : ℝ)^4183 ≤ (2646415924506733/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2247 : ℕ)^4183*20000000000000000000^1024 ≤ 2646415924506733^1024*20000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2247 20000 2646415924506733 20000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2247/20000 : ℝ)) (X := (2646415924506733/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (4183/1024 : ℝ) ≤ (8695883634480267/25000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^4183 ≤ (8695883634480267/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7117 : ℕ)^4183*25000000000000000000^1024 ≤ 8695883634480267^1024*50000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 8695883634480267 25000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (8695883634480267/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002646415924506733/10000000000000000000 : ℝ) ≤ (10000647778902481/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (10002646415924506733/10000000000000000000 : ℝ)^1024 ≤ (10000647778902481/10000000000000000 : ℝ)^4183 := by
      have hnat : (10002646415924506733 : ℕ)^1024*10000000000000000^4183 ≤ 10000647778902481^4183*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002646415924506733 10000000000000000000 10000647778902481 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000647778902481/10000000000000000 : ℝ)) (X := (10002646415924506733/10000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048015614160454733/100000000000000000000 : ℝ) ≤ (10001175211018641/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (100048015614160454733/100000000000000000000 : ℝ)^1024 ≤ (10001175211018641/10000000000000000 : ℝ)^4183 := by
      have hnat : (100048015614160454733 : ℕ)^1024*10000000000000000^4183 ≤ 10001175211018641^4183*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048015614160454733 100000000000000000000 10001175211018641 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001175211018641/10000000000000000 : ℝ)) (X := (100048015614160454733/100000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508695883634480267/12500000000000000000 : ℝ) ≤ (10001702643134801/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (12508695883634480267/12500000000000000000 : ℝ)^1024 ≤ (10001702643134801/10000000000000000 : ℝ)^4183 := by
      have hnat : (12508695883634480267 : ℕ)^1024*10000000000000000^4183 ≤ 10001702643134801^4183*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508695883634480267 12500000000000000000 10001702643134801 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001702643134801/10000000000000000 : ℝ)) (X := (12508695883634480267/12500000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2646415924506733/20000000000000000000 : ℝ) ≤ ((29980091289278425319/29990000000000000000 : ℝ)+2*(1648225363/937187500000 : ℝ)*(2247/20000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (29980091289278425319/29990000000000000000 : ℝ)+2*(1648225363/937187500000 : ℝ)*(2247/20000 : ℝ)=(10000647778902481/10000000000000000 : ℝ) by norm_num, show 1+2*(2646415924506733/20000000000000000000 : ℝ)=(10002646415924506733/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8695883634480267/25000000000000000000 : ℝ)+(2646415924506733/20000000000000000000 : ℝ) ≤ ((29980091289278425319/29990000000000000000 : ℝ)+(1648225363/937187500000 : ℝ)*((7117/50000 : ℝ)+(2247/20000 : ℝ)))^(4183/1024 : ℝ) := by
    rw [show (29980091289278425319/29990000000000000000 : ℝ)+(1648225363/937187500000 : ℝ)*((7117/50000 : ℝ)+(2247/20000 : ℝ))=(10001175211018641/10000000000000000 : ℝ) by norm_num, show 1+(8695883634480267/25000000000000000000 : ℝ)+(2646415924506733/20000000000000000000 : ℝ)=(100048015614160454733/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8695883634480267/25000000000000000000 : ℝ) ≤ ((29980091289278425319/29990000000000000000 : ℝ)+2*(1648225363/937187500000 : ℝ)*(7117/50000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (29980091289278425319/29990000000000000000 : ℝ)+2*(1648225363/937187500000 : ℝ)*(7117/50000 : ℝ)=(10001702643134801/10000000000000000 : ℝ) by norm_num, show 1+2*(8695883634480267/25000000000000000000 : ℝ)=(12508695883634480267/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29980091289278425319/29990000000000000000 : ℝ)*(X 1 0+X 2 0)+(1648225363/937187500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (29980091289278425319/29990000000000000000 : ℝ)) (alpha := (1648225363/937187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29980091289278425319/29990000000000000000 : ℝ)*(X 0 1+X 2 1)+(1648225363/937187500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (29980091289278425319/29990000000000000000 : ℝ)) (alpha := (1648225363/937187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29980091289278425319/29990000000000000000 : ℝ)*(X 0 2+X 1 2)+(1648225363/937187500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (29980091289278425319/29990000000000000000 : ℝ)) (alpha := (1648225363/937187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1075767779/5000000000 : ℝ)*X 0 0+(539408497/1000000000 : ℝ)*X 0 1+(5264702283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672521489/5000000000 : ℝ)*X 1 0+(-277146977/1250000000 : ℝ)*X 1 1+(1316175581/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069008599/2000000000 : ℝ)*X 2 0+(5264702223/10000000000 : ℝ)*X 2 1+(-88687037/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360103239/10000000000 : ℝ)*X 0 0+(423249227/1000000000 : ℝ)*X 0 1+(280719557/625000000 : ℝ)*X 0 2+(4360103239/10000000000 : ℝ)*X 1 0+(423249227/1000000000 : ℝ)*X 1 1+(280719557/625000000 : ℝ)*X 1 2+(4360103239/10000000000 : ℝ)*X 2 0+(423249227/1000000000 : ℝ)*X 2 1+(280719557/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151541187/10000000000 : ℝ)*X 0 0+(5265035249/10000000000 : ℝ)*X 0 1+(1348437607/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656093327/5000000000 : ℝ)*X 1 0+(-1044064107/5000000000 : ℝ)*X 1 1+(5393750313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656093599/5000000000 : ℝ)*X 2 0+(5393749759/10000000000 : ℝ)*X 2 1+(-2088128233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360113369/10000000000 : ℝ)*X 0 0+(4490845229/10000000000 : ℝ)*X 0 1+(4233162669/10000000000 : ℝ)*X 0 2+(4360113369/10000000000 : ℝ)*X 1 0+(4490845229/10000000000 : ℝ)*X 1 1+(4233162669/10000000000 : ℝ)*X 1 2+(4360113369/10000000000 : ℝ)*X 2 0+(4490845229/10000000000 : ℝ)*X 2 1+(4233162669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7361003223237548201248162851/749750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (394741841/20000000000000 : ℝ)*(base19) + (83337151/5000000000000 : ℝ)*(base23) + (194402501/100000000000000 : ℝ)*(lower2) + (414871477/100000000000000 : ℝ)*(upper3) + (17188273/100000000000000 : ℝ)*(lower4) + (5794931863443143/100000000000000 : ℝ)*(major0) + (5794931863443143/100000000000000 : ℝ)*(major1) + (724366482930393/12500000000000 : ℝ)*(major2) + (3864533338027489/50000000000000 : ℝ)*(sp0) + (3864553716374669/50000000000000 : ℝ)*(sp1) + (3864553869857761/50000000000000 : ℝ)*(sp2) + (1930359962085563/50000000000000 : ℝ)*(sp3) + (10682600891/25000000000000 : ℝ)*(sp4) + (34068991817/100000000000000 : ℝ)*(sp7) + (1930376996581471/50000000000000 : ℝ)*(f.failure) + (3864554703229271/50000000000000 : ℝ)*(f.sum) + (7491077005187/2999000000000000000000000000 : ℝ)*base65 + (90308422558862383/2999000000000000000000000000000000 : ℝ)*base68 + (1696419129068195367/374875000000000000000000000000000 : ℝ)*base69 + (23992734116616862383/2999000000000000000000000000000000 : ℝ)*base72 + (2868659327903/2999000000000000000000000000 : ℝ)*base74 + (4837735098013554633/374875000000000000000000000000000 : ℝ)*base76 + (17591088986406862383/2999000000000000000000000000000000 : ℝ)*base78 + (89760061266864862383/2999000000000000000000000000000000 : ℝ)*base80 + (11392304643811/2999000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (50761521/5000000000000000000000 : ℝ)*base90 + (50761521/5000000000000000000000 : ℝ)*base92 + (100761521/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2452569206304395264429775429/374875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (462708279/50000000000000 : ℝ)*(base19) + (2193586127/100000000000000 : ℝ)*(base23) + (253228891/100000000000000 : ℝ)*(upper2) + (49469791/100000000000000 : ℝ)*(upper3) + (498326077/100000000000000 : ℝ)*(upper5) + (1456231297877299/25000000000000 : ℝ)*(major0) + (1456231297877299/25000000000000 : ℝ)*(major1) + (1456231297877299/25000000000000 : ℝ)*(major2) + (22275075729/100000000000000 : ℝ)*(sp1) + (2700988257/12500000000000 : ℝ)*(sp2) + (7769113734738849/100000000000000 : ℝ)*(sp4) + (7769090534246563/100000000000000 : ℝ)*(sp5) + (3884544966623333/50000000000000 : ℝ)*(sp6) + (1940368215100343/50000000000000 : ℝ)*(sp7) + (1940368215100343/50000000000000 : ℝ)*(f.failure) + (7769113734738849/100000000000000 : ℝ)*(f.sum) + (18275146974157/2999000000000000000000000000 : ℝ)*base66 + (10040461555195316619/749750000000000000000000000000000 : ℝ)*base68 + (11046665650242566619/749750000000000000000000000000000 : ℝ)*base70 + (5492258230744566619/749750000000000000000000000000000 : ℝ)*base72 + (137965738689/149950000000000000000000000 : ℝ)*base74 + (25202501247231816619/749750000000000000000000000000000 : ℝ)*base76 + (482884896638566619/749750000000000000000000000000000 : ℝ)*base78 + (11861400059050066619/749750000000000000000000000000000 : ℝ)*base80 + (6391931764643/749750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (63668007/5000000000000000000000 : ℝ)*base89 + (63668007/5000000000000000000000 : ℝ)*base91 + (63668007/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1174_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1174_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1174_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16409/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1174_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1174_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1174_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16409/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1174_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
