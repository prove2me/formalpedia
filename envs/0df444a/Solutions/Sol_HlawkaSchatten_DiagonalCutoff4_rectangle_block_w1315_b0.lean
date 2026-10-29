-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1315_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:41:38.811737+00:00
-- url     : https://prove2.me/submissions/813a3e0a-4d76-4882-a1fc-b0a7e2e7dea7

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
theorem support_rectangle_w1315_s0_0 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-912607963/5000000000 : ℝ)*x 0 + (300432999/500000000 : ℝ)*x 1 + (300276647/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (912607963/5000000000 : ℝ)^4275 ≤ (333805147139/3125000000000 : ℝ)^3251 := by
    have hnat : (912607963 : ℕ)^4275*3125000000000^3251 ≤ 333805147139^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912607963 5000000000 333805147139 3125000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300432999/500000000 : ℝ)^4275 ≤ (51179613853409/100000000000000 : ℝ)^3251 := by
    have hnat : (300432999 : ℕ)^4275*100000000000000^3251 ≤ 51179613853409^3251*500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300432999 500000000 51179613853409 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300276647/625000000 : ℝ)^4275 ≤ (9534655356641/25000000000000 : ℝ)^3251 := by
    have hnat : (300276647 : ℕ)^4275*25000000000000^3251 ≤ 9534655356641^3251*625000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300276647 625000000 9534655356641 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-912607963/5000000000 : ℝ), (300432999/500000000 : ℝ), (300276647/625000000 : ℝ)] ![(333805147139/3125000000000 : ℝ), (51179613853409/100000000000000 : ℝ), (9534655356641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-912607963/5000000000 : ℝ)|^4275 ≤ (333805147139/3125000000000 : ℝ)^3251
        have hw : |(-912607963/5000000000 : ℝ)|=(912607963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300432999/500000000 : ℝ)|^4275 ≤ (51179613853409/100000000000000 : ℝ)^3251
        have hw : |(300432999/500000000 : ℝ)|=(300432999/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300276647/625000000 : ℝ)|^4275 ≤ (9534655356641/25000000000000 : ℝ)^3251
        have hw : |(300276647/625000000 : ℝ)|=(300276647/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s0_1 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1376209681/2500000000 : ℝ)*x 0 + (-1255525687/5000000000 : ℝ)*x 1 + (4804426359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1376209681/2500000000 : ℝ)^4275 ≤ (45612547894543/100000000000000 : ℝ)^3251 := by
    have hnat : (1376209681 : ℕ)^4275*100000000000000^3251 ≤ 45612547894543^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376209681 2500000000 45612547894543 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1255525687/5000000000 : ℝ)^4275 ≤ (4062207647001/25000000000000 : ℝ)^3251 := by
    have hnat : (1255525687 : ℕ)^4275*25000000000000^3251 ≤ 4062207647001^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255525687 5000000000 4062207647001 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4804426359/10000000000 : ℝ)^4275 ≤ (19069310749817/50000000000000 : ℝ)^3251 := by
    have hnat : (4804426359 : ℕ)^4275*50000000000000^3251 ≤ 19069310749817^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4804426359 10000000000 19069310749817 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1376209681/2500000000 : ℝ), (-1255525687/5000000000 : ℝ), (4804426359/10000000000 : ℝ)] ![(45612547894543/100000000000000 : ℝ), (4062207647001/25000000000000 : ℝ), (19069310749817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1376209681/2500000000 : ℝ)|^4275 ≤ (45612547894543/100000000000000 : ℝ)^3251
        have hw : |(1376209681/2500000000 : ℝ)|=(1376209681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1255525687/5000000000 : ℝ)|^4275 ≤ (4062207647001/25000000000000 : ℝ)^3251
        have hw : |(-1255525687/5000000000 : ℝ)|=(1255525687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4804426359/10000000000 : ℝ)|^4275 ≤ (19069310749817/50000000000000 : ℝ)^3251
        have hw : |(4804426359/10000000000 : ℝ)|=(4804426359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s0_2 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2752418983/5000000000 : ℝ)*x 0 + (4804426897/10000000000 : ℝ)*x 1 + (-502210337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2752418983/5000000000 : ℝ)^4275 ≤ (11403134908883/25000000000000 : ℝ)^3251 := by
    have hnat : (2752418983 : ℕ)^4275*25000000000000^3251 ≤ 11403134908883^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752418983 5000000000 11403134908883 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4804426897/10000000000 : ℝ)^4275 ≤ (19069313557803/50000000000000 : ℝ)^3251 := by
    have hnat : (4804426897 : ℕ)^4275*50000000000000^3251 ≤ 19069313557803^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4804426897 10000000000 19069313557803 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502210337/2000000000 : ℝ)^4275 ≤ (16248833234347/100000000000000 : ℝ)^3251 := by
    have hnat : (502210337 : ℕ)^4275*100000000000000^3251 ≤ 16248833234347^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502210337 2000000000 16248833234347 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2752418983/5000000000 : ℝ), (4804426897/10000000000 : ℝ), (-502210337/2000000000 : ℝ)] ![(11403134908883/25000000000000 : ℝ), (19069313557803/50000000000000 : ℝ), (16248833234347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2752418983/5000000000 : ℝ)|^4275 ≤ (11403134908883/25000000000000 : ℝ)^3251
        have hw : |(2752418983/5000000000 : ℝ)|=(2752418983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4804426897/10000000000 : ℝ)|^4275 ≤ (19069313557803/50000000000000 : ℝ)^3251
        have hw : |(4804426897/10000000000 : ℝ)|=(4804426897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-502210337/2000000000 : ℝ)|^4275 ≤ (16248833234347/100000000000000 : ℝ)^3251
        have hw : |(-502210337/2000000000 : ℝ)|=(502210337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s0_3 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4182817367/10000000000 : ℝ)*x 0 + (3108016837/10000000000 : ℝ)*x 1 + (5604770481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182817367/10000000000 : ℝ)^4275 ≤ (794656031007/2500000000000 : ℝ)^3251 := by
    have hnat : (4182817367 : ℕ)^4275*2500000000000^3251 ≤ 794656031007^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182817367 10000000000 794656031007 2500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3108016837/10000000000 : ℝ)^4275 ≤ (2688659357649/12500000000000 : ℝ)^3251 := by
    have hnat : (3108016837 : ℕ)^4275*12500000000000^3251 ≤ 2688659357649^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3108016837 10000000000 2688659357649 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5604770481/10000000000 : ℝ)^4275 ≤ (2919030243019/6250000000000 : ℝ)^3251 := by
    have hnat : (5604770481 : ℕ)^4275*6250000000000^3251 ≤ 2919030243019^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604770481 10000000000 2919030243019 6250000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182817367/10000000000 : ℝ), (3108016837/10000000000 : ℝ), (5604770481/10000000000 : ℝ)] ![(794656031007/2500000000000 : ℝ), (2688659357649/12500000000000 : ℝ), (2919030243019/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182817367/10000000000 : ℝ)|^4275 ≤ (794656031007/2500000000000 : ℝ)^3251
        have hw : |(4182817367/10000000000 : ℝ)|=(4182817367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3108016837/10000000000 : ℝ)|^4275 ≤ (2688659357649/12500000000000 : ℝ)^3251
        have hw : |(3108016837/10000000000 : ℝ)|=(3108016837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5604770481/10000000000 : ℝ)|^4275 ≤ (2919030243019/6250000000000 : ℝ)^3251
        have hw : |(5604770481/10000000000 : ℝ)|=(5604770481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s0_4 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1829815973/10000000000 : ℝ)*x 0 + (2417733899/5000000000 : ℝ)*x 1 + (1494127939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1829815973/10000000000 : ℝ)^4275 ≤ (5358589657551/50000000000000 : ℝ)^3251 := by
    have hnat : (1829815973 : ℕ)^4275*50000000000000^3251 ≤ 5358589657551^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1829815973 10000000000 5358589657551 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2417733899/5000000000 : ℝ)^4275 ≤ (38462980150719/100000000000000 : ℝ)^3251 := by
    have hnat : (2417733899 : ℕ)^4275*100000000000000^3251 ≤ 38462980150719^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417733899 5000000000 38462980150719 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1494127939/2500000000 : ℝ)^4275 ≤ (50819840525873/100000000000000 : ℝ)^3251 := by
    have hnat : (1494127939 : ℕ)^4275*100000000000000^3251 ≤ 50819840525873^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1494127939 2500000000 50819840525873 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1829815973/10000000000 : ℝ), (2417733899/5000000000 : ℝ), (1494127939/2500000000 : ℝ)] ![(5358589657551/50000000000000 : ℝ), (38462980150719/100000000000000 : ℝ), (50819840525873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1829815973/10000000000 : ℝ)|^4275 ≤ (5358589657551/50000000000000 : ℝ)^3251
        have hw : |(-1829815973/10000000000 : ℝ)|=(1829815973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2417733899/5000000000 : ℝ)|^4275 ≤ (38462980150719/100000000000000 : ℝ)^3251
        have hw : |(2417733899/5000000000 : ℝ)|=(2417733899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1494127939/2500000000 : ℝ)|^4275 ≤ (50819840525873/100000000000000 : ℝ)^3251
        have hw : |(1494127939/2500000000 : ℝ)|=(1494127939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s0_5 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (258841379/500000000 : ℝ)*x 0 + (-669483421/5000000000 : ℝ)*x 1 + (1494127919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258841379/500000000 : ℝ)^4275 ≤ (21036306386797/50000000000000 : ℝ)^3251 := by
    have hnat : (258841379 : ℕ)^4275*50000000000000^3251 ≤ 21036306386797^3251*500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258841379 500000000 21036306386797 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (669483421/5000000000 : ℝ)^4275 ≤ (222110861841/3125000000000 : ℝ)^3251 := by
    have hnat : (669483421 : ℕ)^4275*3125000000000^3251 ≤ 222110861841^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669483421 5000000000 222110861841 3125000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1494127919/2500000000 : ℝ)^4275 ≤ (50819839631343/100000000000000 : ℝ)^3251 := by
    have hnat : (1494127919 : ℕ)^4275*100000000000000^3251 ≤ 50819839631343^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1494127919 2500000000 50819839631343 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258841379/500000000 : ℝ), (-669483421/5000000000 : ℝ), (1494127919/2500000000 : ℝ)] ![(21036306386797/50000000000000 : ℝ), (222110861841/3125000000000 : ℝ), (50819839631343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258841379/500000000 : ℝ)|^4275 ≤ (21036306386797/50000000000000 : ℝ)^3251
        have hw : |(258841379/500000000 : ℝ)|=(258841379/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-669483421/5000000000 : ℝ)|^4275 ≤ (222110861841/3125000000000 : ℝ)^3251
        have hw : |(-669483421/5000000000 : ℝ)|=(669483421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1494127919/2500000000 : ℝ)|^4275 ≤ (50819839631343/100000000000000 : ℝ)^3251
        have hw : |(1494127919/2500000000 : ℝ)|=(1494127919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s0_6 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5176827601/10000000000 : ℝ)*x 0 + (5976511721/10000000000 : ℝ)*x 1 + (-1338966737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5176827601/10000000000 : ℝ)^4275 ≤ (42072612998021/100000000000000 : ℝ)^3251 := by
    have hnat : (5176827601 : ℕ)^4275*100000000000000^3251 ≤ 42072612998021^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176827601 10000000000 42072612998021 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5976511721/10000000000 : ℝ)^4275 ≤ (12704960033629/25000000000000 : ℝ)^3251 := by
    have hnat : (5976511721 : ℕ)^4275*25000000000000^3251 ≤ 12704960033629^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5976511721 10000000000 12704960033629 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1338966737/10000000000 : ℝ)^4275 ≤ (7107546845989/100000000000000 : ℝ)^3251 := by
    have hnat : (1338966737 : ℕ)^4275*100000000000000^3251 ≤ 7107546845989^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338966737 10000000000 7107546845989 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5176827601/10000000000 : ℝ), (5976511721/10000000000 : ℝ), (-1338966737/10000000000 : ℝ)] ![(42072612998021/100000000000000 : ℝ), (12704960033629/25000000000000 : ℝ), (7107546845989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5176827601/10000000000 : ℝ)|^4275 ≤ (42072612998021/100000000000000 : ℝ)^3251
        have hw : |(5176827601/10000000000 : ℝ)|=(5176827601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5976511721/10000000000 : ℝ)|^4275 ≤ (12704960033629/25000000000000 : ℝ)^3251
        have hw : |(5976511721/10000000000 : ℝ)|=(5976511721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1338966737/10000000000 : ℝ)|^4275 ≤ (7107546845989/100000000000000 : ℝ)^3251
        have hw : |(-1338966737/10000000000 : ℝ)|=(1338966737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s0_7 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048088503/2500000000 : ℝ)*x 0 + (2770206189/5000000000 : ℝ)*x 1 + (1587334767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048088503/2500000000 : ℝ)^4275 ≤ (31881573716069/100000000000000 : ℝ)^3251 := by
    have hnat : (1048088503 : ℕ)^4275*100000000000000^3251 ≤ 31881573716069^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048088503 2500000000 31881573716069 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2770206189/5000000000 : ℝ)^4275 ≤ (5750068124709/12500000000000 : ℝ)^3251 := by
    have hnat : (2770206189 : ℕ)^4275*12500000000000^3251 ≤ 5750068124709^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2770206189 5000000000 5750068124709 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1587334767/5000000000 : ℝ)^4275 ≤ (11058940633897/50000000000000 : ℝ)^3251 := by
    have hnat : (1587334767 : ℕ)^4275*50000000000000^3251 ≤ 11058940633897^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587334767 5000000000 11058940633897 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048088503/2500000000 : ℝ), (2770206189/5000000000 : ℝ), (1587334767/5000000000 : ℝ)] ![(31881573716069/100000000000000 : ℝ), (5750068124709/12500000000000 : ℝ), (11058940633897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048088503/2500000000 : ℝ)|^4275 ≤ (31881573716069/100000000000000 : ℝ)^3251
        have hw : |(1048088503/2500000000 : ℝ)|=(1048088503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2770206189/5000000000 : ℝ)|^4275 ≤ (5750068124709/12500000000000 : ℝ)^3251
        have hw : |(2770206189/5000000000 : ℝ)|=(2770206189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1587334767/5000000000 : ℝ)|^4275 ≤ (11058940633897/50000000000000 : ℝ)^3251
        have hw : |(1587334767/5000000000 : ℝ)|=(1587334767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1315_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (121/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27067/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2137/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2137 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2137*1^512 ≤ 0^512*1^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2137/512 : ℝ) ≤ (2183065667913498849/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2137 ≤ (2183065667913498849/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2137*100000000000000000000^512 ≤ 2183065667913498849^512*5^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2183065667913498849 100000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2183065667913498849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2137 := by
      have hnat : (1 : ℕ)^512*1^2137 ≤ 1^2137*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102183065667913498849/100000000000000000000 : ℝ) ≤ (2512968757469893/2500000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (102183065667913498849/100000000000000000000 : ℝ)^512 ≤ (2512968757469893/2500000000000000 : ℝ)^2137 := by
      have hnat : (102183065667913498849 : ℕ)^512*2500000000000000^2137 ≤ 2512968757469893^2137*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102183065667913498849 100000000000000000000 2512968757469893 2500000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512968757469893/2500000000000000 : ℝ)) (X := (102183065667913498849/100000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52183065667913498849/50000000000000000000 : ℝ) ≤ (1262968757469893/1250000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (52183065667913498849/50000000000000000000 : ℝ)^512 ≤ (1262968757469893/1250000000000000 : ℝ)^2137 := by
      have hnat : (52183065667913498849 : ℕ)^512*1250000000000000^2137 ≤ 1262968757469893^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52183065667913498849 50000000000000000000 1262968757469893 1250000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1262968757469893/1250000000000000 : ℝ)) (X := (52183065667913498849/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12968757469893/1000000000000000 : ℝ)*(0 : ℝ))^(2137/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(12968757469893/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2183065667913498849/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12968757469893/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2137/512 : ℝ) := by
    rw [show (1 : ℝ)+(12968757469893/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2512968757469893/2500000000000000 : ℝ) by norm_num, show 1+(2183065667913498849/100000000000000000000 : ℝ)+(0 : ℝ)=(102183065667913498849/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2183065667913498849/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12968757469893/1000000000000000 : ℝ)*(2/5 : ℝ))^(2137/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(12968757469893/1000000000000000 : ℝ)*(2/5 : ℝ)=(1262968757469893/1250000000000000 : ℝ) by norm_num, show 1+2*(2183065667913498849/100000000000000000000 : ℝ)=(52183065667913498849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12968757469893/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12968757469893/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12968757469893/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12968757469893/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12968757469893/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12968757469893/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-912607963/5000000000 : ℝ)*X 0 0+(300432999/500000000 : ℝ)*X 0 1+(300276647/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1376209681/2500000000 : ℝ)*X 1 0+(-1255525687/5000000000 : ℝ)*X 1 1+(4804426359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2752418983/5000000000 : ℝ)*X 2 0+(4804426897/10000000000 : ℝ)*X 2 1+(-502210337/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4182817367/10000000000 : ℝ)*X 0 0+(3108016837/10000000000 : ℝ)*X 0 1+(5604770481/10000000000 : ℝ)*X 0 2+(4182817367/10000000000 : ℝ)*X 1 0+(3108016837/10000000000 : ℝ)*X 1 1+(5604770481/10000000000 : ℝ)*X 1 2+(4182817367/10000000000 : ℝ)*X 2 0+(3108016837/10000000000 : ℝ)*X 2 1+(5604770481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1829815973/10000000000 : ℝ)*X 0 0+(2417733899/5000000000 : ℝ)*X 0 1+(1494127939/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((258841379/500000000 : ℝ)*X 1 0+(-669483421/5000000000 : ℝ)*X 1 1+(1494127919/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5176827601/10000000000 : ℝ)*X 2 0+(5976511721/10000000000 : ℝ)*X 2 1+(-1338966737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1048088503/2500000000 : ℝ)*X 0 0+(2770206189/5000000000 : ℝ)*X 0 1+(1587334767/5000000000 : ℝ)*X 0 2+(1048088503/2500000000 : ℝ)*X 1 0+(2770206189/5000000000 : ℝ)*X 1 1+(1587334767/5000000000 : ℝ)*X 1 2+(1048088503/2500000000 : ℝ)*X 2 0+(2770206189/5000000000 : ℝ)*X 2 1+(1587334767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2364174364784227881/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12888401/25000000000000 : ℝ)*(base1) + (659309/100000000000000 : ℝ)*(base16) + (167223733/25000000000000 : ℝ)*(base19) + (555209607/100000000000000 : ℝ)*(base23) + (113253761/100000000000000 : ℝ)*(upper3) + (61546499222403/10000000000000 : ℝ)*(major0) + (61546499222403/10000000000000 : ℝ)*(major1) + (61546499222403/10000000000000 : ℝ)*(major2) + (415203084647271/50000000000000 : ℝ)*(sp0) + (830407237915519/100000000000000 : ℝ)*(sp1) + (415203676130077/50000000000000 : ℝ)*(sp2) + (200260436191167/50000000000000 : ℝ)*(sp3) + (894864411/50000000000000 : ℝ)*(sp4) + (1074236543/100000000000000 : ℝ)*(sp7) + (400521998172481/100000000000000 : ℝ)*(f.failure) + (830407907469761/100000000000000 : ℝ)*(f.sum) + (8002343367121/5000000000000000000000000000 : ℝ)*base66 + (68704284332879/10000000000000000000000000000 : ℝ)*base67 + (55719525292879/10000000000000000000000000000 : ℝ)*base69 + (20282055112879/10000000000000000000000000000 : ℝ)*base71 + (13525884917121/5000000000000000000000000000 : ℝ)*base74 + (74427894242879/10000000000000000000000000000 : ℝ)*base75 + (4117565032879/10000000000000000000000000000 : ℝ)*base77 + (45327694112879/10000000000000000000000000000 : ℝ)*base79 + (1680837017121/5000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2762217/2000000000000000000000 : ℝ)*base90 + (2762217/2000000000000000000000 : ℝ)*base92 + (2762217/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7772185635504532593/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (927860491/50000000000000 : ℝ)*(base19) + (938614323/50000000000000 : ℝ)*(base23) + (83932983/100000000000000 : ℝ)*(base32) + (12864647/5000000000000 : ℝ)*(upper3) + (37544607/20000000000000 : ℝ)*(upper5) + (649545200414343/100000000000000 : ℝ)*(major0) + (649545200414343/100000000000000 : ℝ)*(major1) + (649545200414343/100000000000000 : ℝ)*(major2) + (4115255973/100000000000000 : ℝ)*(sp1) + (2199301141/50000000000000 : ℝ)*(sp2) + (438194998282233/50000000000000 : ℝ)*(sp4) + (109548003198439/12500000000000 : ℝ)*(sp5) + (438191860366769/50000000000000 : ℝ)*(sp6) + (211350030629189/50000000000000 : ℝ)*(sp7) + (422700145191361/100000000000000 : ℝ)*(f.failure) + (438194998282233/50000000000000 : ℝ)*(f.sum) + (68245091975299/50000000000000000000000000000 : ℝ)*base65 + (513606927324701/100000000000000000000000000000 : ℝ)*base68 + (43431866924701/100000000000000000000000000000 : ℝ)*base70 + (737939246924701/100000000000000000000000000000 : ℝ)*base72 + (45201503975299/50000000000000000000000000000 : ℝ)*base73 + (871463879224701/100000000000000000000000000000 : ℝ)*base76 + (498413380724701/100000000000000000000000000000 : ℝ)*base78 + (258318125724701/100000000000000000000000000000 : ℝ)*base80 + (163760689075299/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (22377/2000000000000000000000 : ℝ)*base90 + (22377/2000000000000000000000 : ℝ)*base92 + (22377/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1315_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (121/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27067/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1315_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1315_s1_0 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-402785781/2000000000 : ℝ)*x 0 + (2827234053/5000000000 : ℝ)*x 1 + (2518894279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402785781/2000000000 : ℝ)^4275 ≤ (6078577482397/50000000000000 : ℝ)^3251 := by
    have hnat : (402785781 : ℕ)^4275*50000000000000^3251 ≤ 6078577482397^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402785781 2000000000 6078577482397 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2827234053/5000000000 : ℝ)^4275 ≤ (47249815109097/100000000000000 : ℝ)^3251 := by
    have hnat : (2827234053 : ℕ)^4275*100000000000000^3251 ≤ 47249815109097^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827234053 5000000000 47249815109097 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2518894279/5000000000 : ℝ)^4275 ≤ (10148257478329/25000000000000 : ℝ)^3251 := by
    have hnat : (2518894279 : ℕ)^4275*25000000000000^3251 ≤ 10148257478329^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518894279 5000000000 10148257478329 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402785781/2000000000 : ℝ), (2827234053/5000000000 : ℝ), (2518894279/5000000000 : ℝ)] ![(6078577482397/50000000000000 : ℝ), (47249815109097/100000000000000 : ℝ), (10148257478329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402785781/2000000000 : ℝ)|^4275 ≤ (6078577482397/50000000000000 : ℝ)^3251
        have hw : |(-402785781/2000000000 : ℝ)|=(402785781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2827234053/5000000000 : ℝ)|^4275 ≤ (47249815109097/100000000000000 : ℝ)^3251
        have hw : |(2827234053/5000000000 : ℝ)|=(2827234053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2518894279/5000000000 : ℝ)|^4275 ≤ (10148257478329/25000000000000 : ℝ)^3251
        have hw : |(2518894279/5000000000 : ℝ)|=(2518894279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s1_1 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2704275989/5000000000 : ℝ)*x 0 + (-18750221/80000000 : ℝ)*x 1 + (2518894267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704275989/5000000000 : ℝ)^4275 ≤ (44566328993983/100000000000000 : ℝ)^3251 := by
    have hnat : (2704275989 : ℕ)^4275*100000000000000^3251 ≤ 44566328993983^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704275989 5000000000 44566328993983 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18750221/80000000 : ℝ)^4275 ≤ (3710160330937/25000000000000 : ℝ)^3251 := by
    have hnat : (18750221 : ℕ)^4275*25000000000000^3251 ≤ 3710160330937^3251*80000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18750221 80000000 3710160330937 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2518894267/5000000000 : ℝ)^4275 ≤ (40593029659019/100000000000000 : ℝ)^3251 := by
    have hnat : (2518894267 : ℕ)^4275*100000000000000^3251 ≤ 40593029659019^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518894267 5000000000 40593029659019 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704275989/5000000000 : ℝ), (-18750221/80000000 : ℝ), (2518894267/5000000000 : ℝ)] ![(44566328993983/100000000000000 : ℝ), (3710160330937/25000000000000 : ℝ), (40593029659019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704275989/5000000000 : ℝ)|^4275 ≤ (44566328993983/100000000000000 : ℝ)^3251
        have hw : |(2704275989/5000000000 : ℝ)|=(2704275989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18750221/80000000 : ℝ)|^4275 ≤ (3710160330937/25000000000000 : ℝ)^3251
        have hw : |(-18750221/80000000 : ℝ)|=(18750221/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2518894267/5000000000 : ℝ)|^4275 ≤ (40593029659019/100000000000000 : ℝ)^3251
        have hw : |(2518894267/5000000000 : ℝ)|=(2518894267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s1_2 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2704275923/5000000000 : ℝ)*x 0 + (2518894201/5000000000 : ℝ)*x 1 + (-2343777967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704275923/5000000000 : ℝ)^4275 ≤ (4456632756371/10000000000000 : ℝ)^3251 := by
    have hnat : (2704275923 : ℕ)^4275*10000000000000^3251 ≤ 4456632756371^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704275923 5000000000 4456632756371 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2518894201/5000000000 : ℝ)^4275 ≤ (40593028260383/100000000000000 : ℝ)^3251 := by
    have hnat : (2518894201 : ℕ)^4275*100000000000000^3251 ≤ 40593028260383^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518894201 5000000000 40593028260383 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2343777967/10000000000 : ℝ)^4275 ≤ (3710161042841/25000000000000 : ℝ)^3251 := by
    have hnat : (2343777967 : ℕ)^4275*25000000000000^3251 ≤ 3710161042841^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2343777967 10000000000 3710161042841 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704275923/5000000000 : ℝ), (2518894201/5000000000 : ℝ), (-2343777967/10000000000 : ℝ)] ![(4456632756371/10000000000000 : ℝ), (40593028260383/100000000000000 : ℝ), (3710161042841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704275923/5000000000 : ℝ)|^4275 ≤ (4456632756371/10000000000000 : ℝ)^3251
        have hw : |(2704275923/5000000000 : ℝ)|=(2704275923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2518894201/5000000000 : ℝ)|^4275 ≤ (40593028260383/100000000000000 : ℝ)^3251
        have hw : |(2518894201/5000000000 : ℝ)|=(2518894201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2343777967/10000000000 : ℝ)|^4275 ≤ (3710161042841/25000000000000 : ℝ)^3251
        have hw : |(-2343777967/10000000000 : ℝ)|=(2343777967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s1_3 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074273927/2500000000 : ℝ)*x 0 + (462800637/1250000000 : ℝ)*x 1 + (996195073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074273927/2500000000 : ℝ)^4275 ≤ (3293309101359/10000000000000 : ℝ)^3251 := by
    have hnat : (1074273927 : ℕ)^4275*10000000000000^3251 ≤ 3293309101359^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074273927 2500000000 3293309101359 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (462800637/1250000000 : ℝ)^4275 ≤ (846087003287/3125000000000 : ℝ)^3251 := by
    have hnat : (462800637 : ℕ)^4275*3125000000000^3251 ≤ 846087003287^3251*1250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462800637 1250000000 846087003287 3125000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (996195073/2000000000 : ℝ)^4275 ≤ (1599684994503/4000000000000 : ℝ)^3251 := by
    have hnat : (996195073 : ℕ)^4275*4000000000000^3251 ≤ 1599684994503^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996195073 2000000000 1599684994503 4000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074273927/2500000000 : ℝ), (462800637/1250000000 : ℝ), (996195073/2000000000 : ℝ)] ![(3293309101359/10000000000000 : ℝ), (846087003287/3125000000000 : ℝ), (1599684994503/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074273927/2500000000 : ℝ)|^4275 ≤ (3293309101359/10000000000000 : ℝ)^3251
        have hw : |(1074273927/2500000000 : ℝ)|=(1074273927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(462800637/1250000000 : ℝ)|^4275 ≤ (846087003287/3125000000000 : ℝ)^3251
        have hw : |(462800637/1250000000 : ℝ)|=(462800637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(996195073/2000000000 : ℝ)|^4275 ≤ (1599684994503/4000000000000 : ℝ)^3251
        have hw : |(996195073/2000000000 : ℝ)|=(996195073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s1_4 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014517657/10000000000 : ℝ)*x 0 + (5045688283/10000000000 : ℝ)*x 1 + (2823210769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014517657/10000000000 : ℝ)^4275 ≤ (3040457162227/25000000000000 : ℝ)^3251 := by
    have hnat : (2014517657 : ℕ)^4275*25000000000000^3251 ≤ 3040457162227^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014517657 10000000000 3040457162227 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5045688283/10000000000 : ℝ)^4275 ≤ (40676753891763/100000000000000 : ℝ)^3251 := by
    have hnat : (5045688283 : ℕ)^4275*100000000000000^3251 ≤ 40676753891763^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045688283 10000000000 40676753891763 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2823210769/5000000000 : ℝ)^4275 ≤ (47161417439637/100000000000000 : ℝ)^3251 := by
    have hnat : (2823210769 : ℕ)^4275*100000000000000^3251 ≤ 47161417439637^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823210769 5000000000 47161417439637 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014517657/10000000000 : ℝ), (5045688283/10000000000 : ℝ), (2823210769/5000000000 : ℝ)] ![(3040457162227/25000000000000 : ℝ), (40676753891763/100000000000000 : ℝ), (47161417439637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014517657/10000000000 : ℝ)|^4275 ≤ (3040457162227/25000000000000 : ℝ)^3251
        have hw : |(-2014517657/10000000000 : ℝ)|=(2014517657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5045688283/10000000000 : ℝ)|^4275 ≤ (40676753891763/100000000000000 : ℝ)^3251
        have hw : |(5045688283/10000000000 : ℝ)|=(5045688283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2823210769/5000000000 : ℝ)|^4275 ≤ (47161417439637/100000000000000 : ℝ)^3251
        have hw : |(2823210769/5000000000 : ℝ)|=(2823210769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s1_5 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262444993/500000000 : ℝ)*x 0 + (-1735144937/10000000000 : ℝ)*x 1 + (2823210611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262444993/500000000 : ℝ)^4275 ≤ (10711132786661/25000000000000 : ℝ)^3251 := by
    have hnat : (262444993 : ℕ)^4275*25000000000000^3251 ≤ 10711132786661^3251*500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262444993 500000000 10711132786661 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1735144937/10000000000 : ℝ)^4275 ≤ (2498513717563/25000000000000 : ℝ)^3251 := by
    have hnat : (1735144937 : ℕ)^4275*25000000000000^3251 ≤ 2498513717563^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735144937 10000000000 2498513717563 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2823210611/5000000000 : ℝ)^4275 ≤ (9432282793783/20000000000000 : ℝ)^3251 := by
    have hnat : (2823210611 : ℕ)^4275*20000000000000^3251 ≤ 9432282793783^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823210611 5000000000 9432282793783 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262444993/500000000 : ℝ), (-1735144937/10000000000 : ℝ), (2823210611/5000000000 : ℝ)] ![(10711132786661/25000000000000 : ℝ), (2498513717563/25000000000000 : ℝ), (9432282793783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262444993/500000000 : ℝ)|^4275 ≤ (10711132786661/25000000000000 : ℝ)^3251
        have hw : |(262444993/500000000 : ℝ)|=(262444993/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1735144937/10000000000 : ℝ)|^4275 ≤ (2498513717563/25000000000000 : ℝ)^3251
        have hw : |(-1735144937/10000000000 : ℝ)|=(1735144937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2823210611/5000000000 : ℝ)|^4275 ≤ (9432282793783/20000000000000 : ℝ)^3251
        have hw : |(2823210611/5000000000 : ℝ)|=(2823210611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s1_6 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2624449877/5000000000 : ℝ)*x 0 + (5646421069/10000000000 : ℝ)*x 1 + (-1735145309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624449877/5000000000 : ℝ)^4275 ≤ (535556625111/1250000000000 : ℝ)^3251 := by
    have hnat : (2624449877 : ℕ)^4275*1250000000000^3251 ≤ 535556625111^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624449877 5000000000 535556625111 1250000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5646421069/10000000000 : ℝ)^4275 ≤ (47161412288471/100000000000000 : ℝ)^3251 := by
    have hnat : (5646421069 : ℕ)^4275*100000000000000^3251 ≤ 47161412288471^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5646421069 10000000000 47161412288471 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1735145309/10000000000 : ℝ)^4275 ≤ (9994057687779/100000000000000 : ℝ)^3251 := by
    have hnat : (1735145309 : ℕ)^4275*100000000000000^3251 ≤ 9994057687779^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735145309 10000000000 9994057687779 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624449877/5000000000 : ℝ), (5646421069/10000000000 : ℝ), (-1735145309/10000000000 : ℝ)] ![(535556625111/1250000000000 : ℝ), (47161412288471/100000000000000 : ℝ), (9994057687779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624449877/5000000000 : ℝ)|^4275 ≤ (535556625111/1250000000000 : ℝ)^3251
        have hw : |(2624449877/5000000000 : ℝ)|=(2624449877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5646421069/10000000000 : ℝ)|^4275 ≤ (47161412288471/100000000000000 : ℝ)^3251
        have hw : |(5646421069/10000000000 : ℝ)|=(5646421069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1735145309/10000000000 : ℝ)|^4275 ≤ (9994057687779/100000000000000 : ℝ)^3251
        have hw : |(-1735145309/10000000000 : ℝ)|=(1735145309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s1_7 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149157879/5000000000 : ℝ)*x 0 + (992919239/2000000000 : ℝ)*x 1 + (1859544299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149157879/5000000000 : ℝ)^4275 ≤ (4118173411417/12500000000000 : ℝ)^3251 := by
    have hnat : (2149157879 : ℕ)^4275*12500000000000^3251 ≤ 4118173411417^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149157879 5000000000 4118173411417 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992919239/2000000000 : ℝ)^4275 ≤ (39819284174973/100000000000000 : ℝ)^3251 := by
    have hnat : (992919239 : ℕ)^4275*100000000000000^3251 ≤ 39819284174973^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992919239 2000000000 39819284174973 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1859544299/5000000000 : ℝ)^4275 ≤ (2723532852483/10000000000000 : ℝ)^3251 := by
    have hnat : (1859544299 : ℕ)^4275*10000000000000^3251 ≤ 2723532852483^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859544299 5000000000 2723532852483 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149157879/5000000000 : ℝ), (992919239/2000000000 : ℝ), (1859544299/5000000000 : ℝ)] ![(4118173411417/12500000000000 : ℝ), (39819284174973/100000000000000 : ℝ), (2723532852483/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149157879/5000000000 : ℝ)|^4275 ≤ (4118173411417/12500000000000 : ℝ)^3251
        have hw : |(2149157879/5000000000 : ℝ)|=(2149157879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(992919239/2000000000 : ℝ)|^4275 ≤ (39819284174973/100000000000000 : ℝ)^3251
        have hw : |(992919239/2000000000 : ℝ)|=(992919239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1859544299/5000000000 : ℝ)|^4275 ≤ (2723532852483/10000000000000 : ℝ)^3251
        have hw : |(1859544299/5000000000 : ℝ)|=(1859544299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1315_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (3317/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4917/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (121/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (121/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (121/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (121/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (121/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (121/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (121/10000 : ℝ) ^ (2137/512 : ℝ) ≤ (199024092641/20000000000000000000 : ℝ) := by
    have hpowers : (121/10000 : ℝ)^2137 ≤ (199024092641/20000000000000000000 : ℝ)^512 := by
      have hnat : (121 : ℕ)^2137*20000000000000000000^512 ≤ 199024092641^512*10000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121 10000 199024092641 20000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (121/10000 : ℝ)) (X := (199024092641/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27067/100000 : ℝ) ^ (2137/512 : ℝ) ≤ (427663929949961089/100000000000000000000 : ℝ) := by
    have hpowers : (27067/100000 : ℝ)^2137 ≤ (427663929949961089/100000000000000000000 : ℝ)^512 := by
      have hnat : (27067 : ℕ)^2137*100000000000000000000^512 ≤ 427663929949961089^512*100000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27067 100000 427663929949961089 100000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27067/100000 : ℝ)) (X := (427663929949961089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000199024092641/10000000000000000000 : ℝ) ≤ (5000000023841913/5000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (10000000199024092641/10000000000000000000 : ℝ)^512 ≤ (5000000023841913/5000000000000000 : ℝ)^2137 := by
      have hnat : (10000000199024092641 : ℕ)^512*5000000000000000^2137 ≤ 5000000023841913^2137*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000199024092641 10000000000000000000 5000000023841913 5000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000023841913/5000000000000000 : ℝ)) (X := (10000000199024092641/10000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50213832462535212147/50000000000000000000 : ℝ) ≤ (15640983950539/15625000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50213832462535212147/50000000000000000000 : ℝ)^512 ≤ (15640983950539/15625000000000 : ℝ)^2137 := by
      have hnat : (50213832462535212147 : ℕ)^512*15625000000000^2137 ≤ 15640983950539^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50213832462535212147 50000000000000000000 15640983950539 15625000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (15640983950539/15625000000000 : ℝ)) (X := (50213832462535212147/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50427663929949961089/50000000000000000000 : ℝ) ≤ (5010229704503047/5000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50427663929949961089/50000000000000000000 : ℝ)^512 ≤ (5010229704503047/5000000000000000 : ℝ)^2137 := by
      have hnat : (50427663929949961089 : ℕ)^512*5000000000000000^2137 ≤ 5010229704503047^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50427663929949961089 50000000000000000000 5010229704503047 5000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010229704503047/5000000000000000 : ℝ)) (X := (50427663929949961089/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(199024092641/20000000000000000000 : ℝ) ≤ ((129272622702880372301/129285000000000000000 : ℝ)+2*(5114840330567/1292850000000000 : ℝ)*(121/10000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (129272622702880372301/129285000000000000000 : ℝ)+2*(5114840330567/1292850000000000 : ℝ)*(121/10000 : ℝ)=(5000000023841913/5000000000000000 : ℝ) by norm_num, show 1+2*(199024092641/20000000000000000000 : ℝ)=(10000000199024092641/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(427663929949961089/100000000000000000000 : ℝ)+(199024092641/20000000000000000000 : ℝ) ≤ ((129272622702880372301/129285000000000000000 : ℝ)+(5114840330567/1292850000000000 : ℝ)*((27067/100000 : ℝ)+(121/10000 : ℝ)))^(2137/512 : ℝ) := by
    rw [show (129272622702880372301/129285000000000000000 : ℝ)+(5114840330567/1292850000000000 : ℝ)*((27067/100000 : ℝ)+(121/10000 : ℝ))=(15640983950539/15625000000000 : ℝ) by norm_num, show 1+(427663929949961089/100000000000000000000 : ℝ)+(199024092641/20000000000000000000 : ℝ)=(50213832462535212147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(427663929949961089/100000000000000000000 : ℝ) ≤ ((129272622702880372301/129285000000000000000 : ℝ)+2*(5114840330567/1292850000000000 : ℝ)*(27067/100000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (129272622702880372301/129285000000000000000 : ℝ)+2*(5114840330567/1292850000000000 : ℝ)*(27067/100000 : ℝ)=(5010229704503047/5000000000000000 : ℝ) by norm_num, show 1+2*(427663929949961089/100000000000000000000 : ℝ)=(50427663929949961089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (129272622702880372301/129285000000000000000 : ℝ)*(X 1 0+X 2 0)+(5114840330567/1292850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (121/10000 : ℝ)) (hi := (27067/100000 : ℝ)) (c := (129272622702880372301/129285000000000000000 : ℝ)) (alpha := (5114840330567/1292850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (129272622702880372301/129285000000000000000 : ℝ)*(X 0 1+X 2 1)+(5114840330567/1292850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (121/10000 : ℝ)) (hi := (27067/100000 : ℝ)) (c := (129272622702880372301/129285000000000000000 : ℝ)) (alpha := (5114840330567/1292850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (129272622702880372301/129285000000000000000 : ℝ)*(X 0 2+X 1 2)+(5114840330567/1292850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (121/10000 : ℝ)) (hi := (27067/100000 : ℝ)) (c := (129272622702880372301/129285000000000000000 : ℝ)) (alpha := (5114840330567/1292850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-402785781/2000000000 : ℝ)*X 0 0+(2827234053/5000000000 : ℝ)*X 0 1+(2518894279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2704275989/5000000000 : ℝ)*X 1 0+(-18750221/80000000 : ℝ)*X 1 1+(2518894267/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2704275923/5000000000 : ℝ)*X 2 0+(2518894201/5000000000 : ℝ)*X 2 1+(-2343777967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1074273927/2500000000 : ℝ)*X 0 0+(462800637/1250000000 : ℝ)*X 0 1+(996195073/2000000000 : ℝ)*X 0 2+(1074273927/2500000000 : ℝ)*X 1 0+(462800637/1250000000 : ℝ)*X 1 1+(996195073/2000000000 : ℝ)*X 1 2+(1074273927/2500000000 : ℝ)*X 2 0+(462800637/1250000000 : ℝ)*X 2 1+(996195073/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2014517657/10000000000 : ℝ)*X 0 0+(5045688283/10000000000 : ℝ)*X 0 1+(2823210769/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262444993/500000000 : ℝ)*X 1 0+(-1735144937/10000000000 : ℝ)*X 1 1+(2823210611/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2624449877/5000000000 : ℝ)*X 2 0+(5646421069/10000000000 : ℝ)*X 2 1+(-1735145309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2149157879/5000000000 : ℝ)*X 0 0+(992919239/2000000000 : ℝ)*X 0 1+(1859544299/5000000000 : ℝ)*X 0 2+(2149157879/5000000000 : ℝ)*X 1 0+(992919239/2000000000 : ℝ)*X 1 1+(1859544299/5000000000 : ℝ)*X 1 2+(2149157879/5000000000 : ℝ)*X 2 0+(992919239/2000000000 : ℝ)*X 2 1+(1859544299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (893955254960441692316536213/134671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77330637/100000000000000 : ℝ)*(base1) + (562641747/50000000000000 : ℝ)*(base19) + (542853551/50000000000000 : ℝ)*(base23) + (206389293/100000000000000 : ℝ)*(upper3) + (119833/195312500000 : ℝ)*(upper5) + (9389565559957/781250000000 : ℝ)*(major0) + (9389565559957/781250000000 : ℝ)*(major1) + (9389565559957/781250000000 : ℝ)*(major2) + (810797191617271/50000000000000 : ℝ)*(sp0) + (1621598260049303/100000000000000 : ℝ)*(sp1) + (324319659925139/20000000000000 : ℝ)*(sp2) + (391063001413141/50000000000000 : ℝ)*(sp3) + (5079428891/100000000000000 : ℝ)*(sp4) + (123863671/4000000000000 : ℝ)*(sp7) + (156425835349739/20000000000000 : ℝ)*(f.failure) + (1621599385332797/100000000000000 : ℝ)*(f.sum) + (7225822662899/129285000000000000000000000000 : ℝ)*base65 + (109992257005103617/11882812500000000000000000000000 : ℝ)*base67 + (66030385569072367/11882812500000000000000000000000 : ℝ)*base69 + (12076576803690379/5941406250000000000000000000000 : ℝ)*base72 + (143191543405597/64642500000000000000000000000 : ℝ)*base73 + (2715587763072367/11882812500000000000000000000000 : ℝ)*base75 + (211124775341437/742675781250000000000000000000 : ℝ)*base77 + (13097908994816609/23765625000000000000000000000000 : ℝ)*base79 + (107545527656311/129285000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (300323/400000000000000000000 : ℝ)*base90 + (300323/400000000000000000000 : ℝ)*base92 + (300323/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2079862444375736930879189621/359125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (521101221/50000000000000 : ℝ)*(base19) + (243862817/25000000000000 : ℝ)*(base23) + (6449877/100000000000000 : ℝ)*(upper2) + (23879093/25000000000000 : ℝ)*(upper3) + (166814031/100000000000000 : ℝ)*(upper5) + (616879545831321/50000000000000 : ℝ)*(major0) + (616879545831321/50000000000000 : ℝ)*(major1) + (616879545831321/50000000000000 : ℝ)*(major2) + (313830777/6250000000000 : ℝ)*(sp1) + (3527933489/100000000000000 : ℝ)*(sp2) + (832316457463827/50000000000000 : ℝ)*(sp4) + (83231342571639/5000000000000 : ℝ)*(sp5) + (1664628411542897/100000000000000 : ℝ)*(sp6) + (802885075348553/100000000000000 : ℝ)*(sp7) + (802885075348553/100000000000000 : ℝ)*(f.failure) + (832316457463827/50000000000000 : ℝ)*(f.sum) + (508479175361/10773750000000000000000000000 : ℝ)*base66 + (435472643079213929/126750000000000000000000000000000 : ℝ)*base68 + (1190025105804963929/126750000000000000000000000000000 : ℝ)*base70 + (399869271921963929/126750000000000000000000000000000 : ℝ)*base72 + (16735012531051/43095000000000000000000000000 : ℝ)*base73 + (1523582940297963929/126750000000000000000000000000000 : ℝ)*base76 + (700073698209963929/126750000000000000000000000000000 : ℝ)*base78 + (530435440134963929/126750000000000000000000000000000 : ℝ)*base80 + (4265838733583/21547500000000000000000000000 : ℝ)*base81 + (14192079/2000000000000000000000 : ℝ)*base89 + (14192079/2000000000000000000000 : ℝ)*base91 + (14192079/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1315_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3317/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4917/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1315_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1315_s2_0 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1028246157/5000000000 : ℝ)*x 0 + (5487373001/10000000000 : ℝ)*x 1 + (5177661077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1028246157/5000000000 : ℝ)^4275 ≤ (2499227858117/20000000000000 : ℝ)^3251 := by
    have hnat : (1028246157 : ℕ)^4275*20000000000000^3251 ≤ 2499227858117^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028246157 5000000000 2499227858117 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487373001/10000000000 : ℝ)^4275 ≤ (22711170067801/50000000000000 : ℝ)^3251 := by
    have hnat : (5487373001 : ℕ)^4275*50000000000000^3251 ≤ 22711170067801^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487373001 10000000000 22711170067801 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177661077/10000000000 : ℝ)^4275 ≤ (420815205639/1000000000000 : ℝ)^3251 := by
    have hnat : (5177661077 : ℕ)^4275*1000000000000^3251 ≤ 420815205639^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177661077 10000000000 420815205639 1000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1028246157/5000000000 : ℝ), (5487373001/10000000000 : ℝ), (5177661077/10000000000 : ℝ)] ![(2499227858117/20000000000000 : ℝ), (22711170067801/50000000000000 : ℝ), (420815205639/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1028246157/5000000000 : ℝ)|^4275 ≤ (2499227858117/20000000000000 : ℝ)^3251
        have hw : |(-1028246157/5000000000 : ℝ)|=(1028246157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487373001/10000000000 : ℝ)|^4275 ≤ (22711170067801/50000000000000 : ℝ)^3251
        have hw : |(5487373001/10000000000 : ℝ)|=(5487373001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177661077/10000000000 : ℝ)|^4275 ≤ (420815205639/1000000000000 : ℝ)^3251
        have hw : |(5177661077/10000000000 : ℝ)|=(5177661077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s2_1 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683943167/5000000000 : ℝ)*x 0 + (-2216769017/10000000000 : ℝ)*x 1 + (103553213/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683943167/5000000000 : ℝ)^4275 ≤ (44126223079251/100000000000000 : ℝ)^3251 := by
    have hnat : (2683943167 : ℕ)^4275*100000000000000^3251 ≤ 44126223079251^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683943167 5000000000 44126223079251 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216769017/10000000000 : ℝ)^4275 ≤ (13792260901459/100000000000000 : ℝ)^3251 := by
    have hnat : (2216769017 : ℕ)^4275*100000000000000^3251 ≤ 13792260901459^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216769017 10000000000 13792260901459 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103553213/200000000 : ℝ)^4275 ≤ (42081516000329/100000000000000 : ℝ)^3251 := by
    have hnat : (103553213 : ℕ)^4275*100000000000000^3251 ≤ 42081516000329^3251*200000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103553213 200000000 42081516000329 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683943167/5000000000 : ℝ), (-2216769017/10000000000 : ℝ), (103553213/200000000 : ℝ)] ![(44126223079251/100000000000000 : ℝ), (13792260901459/100000000000000 : ℝ), (42081516000329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683943167/5000000000 : ℝ)|^4275 ≤ (44126223079251/100000000000000 : ℝ)^3251
        have hw : |(2683943167/5000000000 : ℝ)|=(2683943167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2216769017/10000000000 : ℝ)|^4275 ≤ (13792260901459/100000000000000 : ℝ)^3251
        have hw : |(-2216769017/10000000000 : ℝ)|=(2216769017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103553213/200000000 : ℝ)|^4275 ≤ (42081516000329/100000000000000 : ℝ)^3251
        have hw : |(103553213/200000000 : ℝ)|=(103553213/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s2_2 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683942859/5000000000 : ℝ)*x 0 + (1035532249/2000000000 : ℝ)*x 1 + (-1108384527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683942859/5000000000 : ℝ)^4275 ≤ (11031554105123/25000000000000 : ℝ)^3251 := by
    have hnat : (2683942859 : ℕ)^4275*25000000000000^3251 ≤ 11031554105123^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683942859 5000000000 11031554105123 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035532249/2000000000 : ℝ)^4275 ≤ (10520380589851/25000000000000 : ℝ)^3251 := by
    have hnat : (1035532249 : ℕ)^4275*25000000000000^3251 ≤ 10520380589851^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035532249 2000000000 10520380589851 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108384527/5000000000 : ℝ)^4275 ≤ (551690448167/4000000000000 : ℝ)^3251 := by
    have hnat : (1108384527 : ℕ)^4275*4000000000000^3251 ≤ 551690448167^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108384527 5000000000 551690448167 4000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683942859/5000000000 : ℝ), (1035532249/2000000000 : ℝ), (-1108384527/5000000000 : ℝ)] ![(11031554105123/25000000000000 : ℝ), (10520380589851/25000000000000 : ℝ), (551690448167/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683942859/5000000000 : ℝ)|^4275 ≤ (11031554105123/25000000000000 : ℝ)^3251
        have hw : |(2683942859/5000000000 : ℝ)|=(2683942859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035532249/2000000000 : ℝ)|^4275 ≤ (10520380589851/25000000000000 : ℝ)^3251
        have hw : |(1035532249/2000000000 : ℝ)|=(1035532249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1108384527/5000000000 : ℝ)|^4275 ≤ (551690448167/4000000000000 : ℝ)^3251
        have hw : |(-1108384527/5000000000 : ℝ)|=(1108384527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s2_3 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (86535303/200000000 : ℝ)*x 0 + (4016930243/10000000000 : ℝ)*x 1 + (4659068587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86535303/200000000 : ℝ)^4275 ≤ (16616212919671/50000000000000 : ℝ)^3251 := by
    have hnat : (86535303 : ℕ)^4275*50000000000000^3251 ≤ 16616212919671^3251*200000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86535303 200000000 16616212919671 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4016930243/10000000000 : ℝ)^4275 ≤ (15069502514263/50000000000000 : ℝ)^3251 := by
    have hnat : (4016930243 : ℕ)^4275*50000000000000^3251 ≤ 15069502514263^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016930243 10000000000 15069502514263 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4659068587/10000000000 : ℝ)^4275 ≤ (36628569123799/100000000000000 : ℝ)^3251 := by
    have hnat : (4659068587 : ℕ)^4275*100000000000000^3251 ≤ 36628569123799^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4659068587 10000000000 36628569123799 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86535303/200000000 : ℝ), (4016930243/10000000000 : ℝ), (4659068587/10000000000 : ℝ)] ![(16616212919671/50000000000000 : ℝ), (15069502514263/50000000000000 : ℝ), (36628569123799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86535303/200000000 : ℝ)|^4275 ≤ (16616212919671/50000000000000 : ℝ)^3251
        have hw : |(86535303/200000000 : ℝ)|=(86535303/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4016930243/10000000000 : ℝ)|^4275 ≤ (15069502514263/50000000000000 : ℝ)^3251
        have hw : |(4016930243/10000000000 : ℝ)|=(4016930243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4659068587/10000000000 : ℝ)|^4275 ≤ (36628569123799/100000000000000 : ℝ)^3251
        have hw : |(4659068587/10000000000 : ℝ)|=(4659068587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s2_4 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2056566459/10000000000 : ℝ)*x 0 + (5179662893/10000000000 : ℝ)*x 1 + (2742676409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2056566459/10000000000 : ℝ)^4275 ≤ (3124182935333/25000000000000 : ℝ)^3251 := by
    have hnat : (2056566459 : ℕ)^4275*25000000000000^3251 ≤ 3124182935333^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056566459 10000000000 3124182935333 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179662893/10000000000 : ℝ)^4275 ≤ (2105145815787/5000000000000 : ℝ)^3251 := by
    have hnat : (5179662893 : ℕ)^4275*5000000000000^3251 ≤ 2105145815787^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179662893 10000000000 2105145815787 5000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2742676409/5000000000 : ℝ)^4275 ≤ (22700175967223/50000000000000 : ℝ)^3251 := by
    have hnat : (2742676409 : ℕ)^4275*50000000000000^3251 ≤ 22700175967223^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742676409 5000000000 22700175967223 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2056566459/10000000000 : ℝ), (5179662893/10000000000 : ℝ), (2742676409/5000000000 : ℝ)] ![(3124182935333/25000000000000 : ℝ), (2105145815787/5000000000000 : ℝ), (22700175967223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2056566459/10000000000 : ℝ)|^4275 ≤ (3124182935333/25000000000000 : ℝ)^3251
        have hw : |(-2056566459/10000000000 : ℝ)|=(2056566459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179662893/10000000000 : ℝ)|^4275 ≤ (2105145815787/5000000000000 : ℝ)^3251
        have hw : |(5179662893/10000000000 : ℝ)|=(5179662893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2742676409/5000000000 : ℝ)|^4275 ≤ (22700175967223/50000000000000 : ℝ)^3251
        have hw : |(2742676409/5000000000 : ℝ)|=(2742676409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s2_5 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82629629/156250000 : ℝ)*x 0 + (-1909076383/10000000000 : ℝ)*x 1 + (5485352897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82629629/156250000 : ℝ)^4275 ≤ (8653579226299/20000000000000 : ℝ)^3251 := by
    have hnat : (82629629 : ℕ)^4275*20000000000000^3251 ≤ 8653579226299^3251*156250000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82629629 156250000 8653579226299 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1909076383/10000000000 : ℝ)^4275 ≤ (177058610331/1562500000000 : ℝ)^3251 := by
    have hnat : (1909076383 : ℕ)^4275*1562500000000^3251 ≤ 177058610331^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909076383 10000000000 177058610331 1562500000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485352897/10000000000 : ℝ)^4275 ≤ (11350088198563/25000000000000 : ℝ)^3251 := by
    have hnat : (5485352897 : ℕ)^4275*25000000000000^3251 ≤ 11350088198563^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485352897 10000000000 11350088198563 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82629629/156250000 : ℝ), (-1909076383/10000000000 : ℝ), (5485352897/10000000000 : ℝ)] ![(8653579226299/20000000000000 : ℝ), (177058610331/1562500000000 : ℝ), (11350088198563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82629629/156250000 : ℝ)|^4275 ≤ (8653579226299/20000000000000 : ℝ)^3251
        have hw : |(82629629/156250000 : ℝ)|=(82629629/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1909076383/10000000000 : ℝ)|^4275 ≤ (177058610331/1562500000000 : ℝ)^3251
        have hw : |(-1909076383/10000000000 : ℝ)|=(1909076383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485352897/10000000000 : ℝ)|^4275 ≤ (11350088198563/25000000000000 : ℝ)^3251
        have hw : |(5485352897/10000000000 : ℝ)|=(5485352897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s2_6 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644148181/5000000000 : ℝ)*x 0 + (685669103/1250000000 : ℝ)*x 1 + (-954538169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644148181/5000000000 : ℝ)^4275 ≤ (21633948635971/50000000000000 : ℝ)^3251 := by
    have hnat : (2644148181 : ℕ)^4275*50000000000000^3251 ≤ 21633948635971^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644148181 5000000000 21633948635971 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685669103/1250000000 : ℝ)^4275 ≤ (45400351999747/100000000000000 : ℝ)^3251 := by
    have hnat : (685669103 : ℕ)^4275*100000000000000^3251 ≤ 45400351999747^3251*1250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685669103 1250000000 45400351999747 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (954538169/5000000000 : ℝ)^4275 ≤ (11331750709943/100000000000000 : ℝ)^3251 := by
    have hnat : (954538169 : ℕ)^4275*100000000000000^3251 ≤ 11331750709943^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954538169 5000000000 11331750709943 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644148181/5000000000 : ℝ), (685669103/1250000000 : ℝ), (-954538169/5000000000 : ℝ)] ![(21633948635971/50000000000000 : ℝ), (45400351999747/100000000000000 : ℝ), (11331750709943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644148181/5000000000 : ℝ)|^4275 ≤ (21633948635971/50000000000000 : ℝ)^3251
        have hw : |(2644148181/5000000000 : ℝ)|=(2644148181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685669103/1250000000 : ℝ)|^4275 ≤ (45400351999747/100000000000000 : ℝ)^3251
        have hw : |(685669103/1250000000 : ℝ)|=(685669103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-954538169/5000000000 : ℝ)|^4275 ≤ (11331750709943/100000000000000 : ℝ)^3251
        have hw : |(-954538169/5000000000 : ℝ)|=(954538169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s2_7 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326917513/10000000000 : ℝ)*x 0 + (2327458051/5000000000 : ℝ)*x 1 + (4021124023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326917513/10000000000 : ℝ)^4275 ≤ (8308491175441/25000000000000 : ℝ)^3251 := by
    have hnat : (4326917513 : ℕ)^4275*25000000000000^3251 ≤ 8308491175441^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326917513 10000000000 8308491175441 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2327458051/5000000000 : ℝ)^4275 ≤ (9146411604423/25000000000000 : ℝ)^3251 := by
    have hnat : (2327458051 : ℕ)^4275*25000000000000^3251 ≤ 9146411604423^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2327458051 5000000000 9146411604423 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021124023/10000000000 : ℝ)^4275 ≤ (30180388869851/100000000000000 : ℝ)^3251 := by
    have hnat : (4021124023 : ℕ)^4275*100000000000000^3251 ≤ 30180388869851^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021124023 10000000000 30180388869851 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326917513/10000000000 : ℝ), (2327458051/5000000000 : ℝ), (4021124023/10000000000 : ℝ)] ![(8308491175441/25000000000000 : ℝ), (9146411604423/25000000000000 : ℝ), (30180388869851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326917513/10000000000 : ℝ)|^4275 ≤ (8308491175441/25000000000000 : ℝ)^3251
        have hw : |(4326917513/10000000000 : ℝ)|=(4326917513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2327458051/5000000000 : ℝ)|^4275 ≤ (9146411604423/25000000000000 : ℝ)^3251
        have hw : |(2327458051/5000000000 : ℝ)|=(2327458051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021124023/10000000000 : ℝ)|^4275 ≤ (30180388869851/100000000000000 : ℝ)^3251
        have hw : |(4021124023/10000000000 : ℝ)|=(4021124023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1315_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4917/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3317/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9669/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3243/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4917/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3317/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4917/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3317/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4917/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3317/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4917/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3317/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4917/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3317/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4917/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3317/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3317/50000 : ℝ) ^ (2137/512 : ℝ) ≤ (1208629826014293/100000000000000000000 : ℝ) := by
    have hpowers : (3317/50000 : ℝ)^2137 ≤ (1208629826014293/100000000000000000000 : ℝ)^512 := by
      have hnat : (3317 : ℕ)^2137*100000000000000000000^512 ≤ 1208629826014293^512*50000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3317 50000 1208629826014293 100000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3317/50000 : ℝ)) (X := (1208629826014293/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hpowhi : (4917/25000 : ℝ) ^ (2137/512 : ℝ) ≤ (112791522295964747/100000000000000000000 : ℝ) := by
    have hpowers : (4917/25000 : ℝ)^2137 ≤ (112791522295964747/100000000000000000000 : ℝ)^512 := by
      have hnat : (4917 : ℕ)^2137*100000000000000000000^512 ≤ 112791522295964747^512*25000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4917 25000 112791522295964747 100000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4917/25000 : ℝ)) (X := (112791522295964747/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001208629826014293/50000000000000000000 : ℝ) ≤ (10000057914158513/10000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50001208629826014293/50000000000000000000 : ℝ)^512 ≤ (10000057914158513/10000000000000000 : ℝ)^2137 := by
      have hnat : (50001208629826014293 : ℕ)^512*10000000000000000^2137 ≤ 10000057914158513^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001208629826014293 50000000000000000000 10000057914158513 10000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000057914158513/10000000000000000 : ℝ)) (X := (50001208629826014293/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (625712500950762369/625000000000000000 : ℝ) ≤ (1000273012615871/1000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (625712500950762369/625000000000000000 : ℝ)^512 ≤ (1000273012615871/1000000000000000 : ℝ)^2137 := by
      have hnat : (625712500950762369 : ℕ)^512*1000000000000000^2137 ≤ 1000273012615871^2137*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625712500950762369 625000000000000000 1000273012615871 1000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000273012615871/1000000000000000 : ℝ)) (X := (625712500950762369/625000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50112791522295964747/50000000000000000000 : ℝ) ≤ (10005402338158907/10000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50112791522295964747/50000000000000000000 : ℝ)^512 ≤ (10005402338158907/10000000000000000 : ℝ)^2137 := by
      have hnat : (50112791522295964747 : ℕ)^512*10000000000000000^2137 ≤ 10005402338158907^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50112791522295964747 50000000000000000000 10005402338158907 10000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005402338158907/10000000000000000 : ℝ)) (X := (50112791522295964747/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1208629826014293/100000000000000000000 : ℝ) ≤ ((65152649972161722323/65170000000000000000 : ℝ)+2*(2672212000197/1303400000000000 : ℝ)*(3317/50000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (65152649972161722323/65170000000000000000 : ℝ)+2*(2672212000197/1303400000000000 : ℝ)*(3317/50000 : ℝ)=(10000057914158513/10000000000000000 : ℝ) by norm_num, show 1+2*(1208629826014293/100000000000000000000 : ℝ)=(50001208629826014293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(112791522295964747/100000000000000000000 : ℝ)+(1208629826014293/100000000000000000000 : ℝ) ≤ ((65152649972161722323/65170000000000000000 : ℝ)+(2672212000197/1303400000000000 : ℝ)*((4917/25000 : ℝ)+(3317/50000 : ℝ)))^(2137/512 : ℝ) := by
    rw [show (65152649972161722323/65170000000000000000 : ℝ)+(2672212000197/1303400000000000 : ℝ)*((4917/25000 : ℝ)+(3317/50000 : ℝ))=(1000273012615871/1000000000000000 : ℝ) by norm_num, show 1+(112791522295964747/100000000000000000000 : ℝ)+(1208629826014293/100000000000000000000 : ℝ)=(625712500950762369/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(112791522295964747/100000000000000000000 : ℝ) ≤ ((65152649972161722323/65170000000000000000 : ℝ)+2*(2672212000197/1303400000000000 : ℝ)*(4917/25000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (65152649972161722323/65170000000000000000 : ℝ)+2*(2672212000197/1303400000000000 : ℝ)*(4917/25000 : ℝ)=(10005402338158907/10000000000000000 : ℝ) by norm_num, show 1+2*(112791522295964747/100000000000000000000 : ℝ)=(50112791522295964747/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (65152649972161722323/65170000000000000000 : ℝ)*(X 1 0+X 2 0)+(2672212000197/1303400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (3317/50000 : ℝ)) (hi := (4917/25000 : ℝ)) (c := (65152649972161722323/65170000000000000000 : ℝ)) (alpha := (2672212000197/1303400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (65152649972161722323/65170000000000000000 : ℝ)*(X 0 1+X 2 1)+(2672212000197/1303400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (3317/50000 : ℝ)) (hi := (4917/25000 : ℝ)) (c := (65152649972161722323/65170000000000000000 : ℝ)) (alpha := (2672212000197/1303400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (65152649972161722323/65170000000000000000 : ℝ)*(X 0 2+X 1 2)+(2672212000197/1303400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (3317/50000 : ℝ)) (hi := (4917/25000 : ℝ)) (c := (65152649972161722323/65170000000000000000 : ℝ)) (alpha := (2672212000197/1303400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1028246157/5000000000 : ℝ)*X 0 0+(5487373001/10000000000 : ℝ)*X 0 1+(5177661077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2683943167/5000000000 : ℝ)*X 1 0+(-2216769017/10000000000 : ℝ)*X 1 1+(103553213/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2683942859/5000000000 : ℝ)*X 2 0+(1035532249/2000000000 : ℝ)*X 2 1+(-1108384527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86535303/200000000 : ℝ)*X 0 0+(4016930243/10000000000 : ℝ)*X 0 1+(4659068587/10000000000 : ℝ)*X 0 2+(86535303/200000000 : ℝ)*X 1 0+(4016930243/10000000000 : ℝ)*X 1 1+(4659068587/10000000000 : ℝ)*X 1 2+(86535303/200000000 : ℝ)*X 2 0+(4016930243/10000000000 : ℝ)*X 2 1+(4659068587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2056566459/10000000000 : ℝ)*X 0 0+(5179662893/10000000000 : ℝ)*X 0 1+(2742676409/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82629629/156250000 : ℝ)*X 1 0+(-1909076383/10000000000 : ℝ)*X 1 1+(5485352897/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644148181/5000000000 : ℝ)*X 2 0+(685669103/1250000000 : ℝ)*X 2 1+(-954538169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326917513/10000000000 : ℝ)*X 0 0+(2327458051/5000000000 : ℝ)*X 0 1+(4021124023/10000000000 : ℝ)*X 0 2+(4326917513/10000000000 : ℝ)*X 1 0+(2327458051/5000000000 : ℝ)*X 1 1+(4021124023/10000000000 : ℝ)*X 1 2+(4326917513/10000000000 : ℝ)*X 2 0+(2327458051/5000000000 : ℝ)*X 2 1+(4021124023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4068965696445980767218543/612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (581689281/25000000000000 : ℝ)*(base19) + (35327299/2500000000000 : ℝ)*(base23) + (291548989/100000000000000 : ℝ)*(lower2) + (143395023/20000000000000 : ℝ)*(upper3) + (82365593/50000000000000 : ℝ)*(upper5) + (59827050209417/2500000000000 : ℝ)*(major0) + (59827050209417/2500000000000 : ℝ)*(major1) + (59827050209417/2500000000000 : ℝ)*(major2) + (322882528784039/10000000000000 : ℝ)*(sp0) + (100900988904191/3125000000000 : ℝ)*(sp1) + (807208139649819/25000000000000 : ℝ)*(sp2) + (6083244397811/390625000000 : ℝ)*(sp3) + (4341925423/50000000000000 : ℝ)*(sp4) + (19257782187/100000000000000 : ℝ)*(sp7) + (778664911810901/50000000000000 : ℝ)*(f.failure) + (807208492922809/25000000000000 : ℝ)*(f.sum) + (30829271971373/6517000000000000000000000000 : ℝ)*base66 + (1872461267156584309/162925000000000000000000000000000 : ℝ)*base68 + (3151040510330509309/162925000000000000000000000000000 : ℝ)*base70 + (2223303816990409309/162925000000000000000000000000000 : ℝ)*base72 + (2987249361199/651700000000000000000000000 : ℝ)*base74 + (2443263149620859309/162925000000000000000000000000000 : ℝ)*base76 + (2482405849263409309/162925000000000000000000000000000 : ℝ)*base78 + (1509805002926184309/162925000000000000000000000000000 : ℝ)*base80 + (46975331279717/6517000000000000000000000000 : ℝ)*base82 + (9391843/1000000000000000000000 : ℝ)*base89 + (9391843/1000000000000000000000 : ℝ)*base91 + (9391843/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13174210389243415159840749/4900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115519101/20000000000000 : ℝ)*(base19) + (793303789/100000000000000 : ℝ)*(base23) + (103128801/100000000000000 : ℝ)*(upper3) + (52406143/100000000000000 : ℝ)*(lower4) + (94367/100000000000000 : ℝ)*(upper5) + (484909180696407/20000000000000 : ℝ)*(major0) + (484909180696407/20000000000000 : ℝ)*(major1) + (484909180696407/20000000000000 : ℝ)*(major2) + (596304751/10000000000000 : ℝ)*(sp1) + (9354404513/100000000000000 : ℝ)*(sp2) + (817821586776817/25000000000000 : ℝ)*(sp4) + (817819951616063/25000000000000 : ℝ)*(sp5) + (1635638099699483/50000000000000 : ℝ)*(sp6) + (788902685118159/50000000000000 : ℝ)*(sp7) + (788902685118159/50000000000000 : ℝ)*(f.failure) + (817821586776817/25000000000000 : ℝ)*(f.sum) + (40659792439969/13034000000000000000000000000 : ℝ)*base66 + (8676323409522743461/1303400000000000000000000000000000 : ℝ)*base67 + (3367901348877543461/1303400000000000000000000000000000 : ℝ)*base69 + (4339641511154343461/1303400000000000000000000000000000 : ℝ)*base71 + (55133315177679/13034000000000000000000000000 : ℝ)*base73 + (13833501702589543461/1303400000000000000000000000000000 : ℝ)*base75 + (5879846284837256539/1303400000000000000000000000000000 : ℝ)*base78 + (2159847464950256539/1303400000000000000000000000000000 : ℝ)*base80 + (32208778996643/13034000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2443737/1000000000000000000000 : ℝ)*base89 + (2443737/1000000000000000000000 : ℝ)*base91 + (2443737/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1315_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4917/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3317/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3243/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1315_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1315_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3243/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1315_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1315_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1315_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3243/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1315_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
