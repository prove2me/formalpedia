-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1283_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:23:41.236987+00:00
-- url     : https://prove2.me/submissions/8e2fafaf-7bd4-45ee-aee5-c8314c573ade

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
theorem support_rectangle_w1283_s0_0 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1801314/9765625 : ℝ)*x 0 + (6022790917/10000000000 : ℝ)*x 1 + (1199159637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1801314/9765625 : ℝ)^4243 ≤ (10773592886561/100000000000000 : ℝ)^3219 := by
    have hnat : (1801314 : ℕ)^4243*100000000000000^3219 ≤ 10773592886561^3219*9765625^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801314 9765625 10773592886561 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6022790917/10000000000 : ℝ)^4243 ≤ (51256505400657/100000000000000 : ℝ)^3219 := by
    have hnat : (6022790917 : ℕ)^4243*100000000000000^3219 ≤ 51256505400657^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6022790917 10000000000 51256505400657 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199159637/2500000000 : ℝ)^4243 ≤ (37969901692303/100000000000000 : ℝ)^3219 := by
    have hnat : (1199159637 : ℕ)^4243*100000000000000^3219 ≤ 37969901692303^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199159637 2500000000 37969901692303 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1801314/9765625 : ℝ), (6022790917/10000000000 : ℝ), (1199159637/2500000000 : ℝ)] ![(10773592886561/100000000000000 : ℝ), (51256505400657/100000000000000 : ℝ), (37969901692303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1801314/9765625 : ℝ)|^4243 ≤ (10773592886561/100000000000000 : ℝ)^3219
        have hw : |(-1801314/9765625 : ℝ)|=(1801314/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6022790917/10000000000 : ℝ)|^4243 ≤ (51256505400657/100000000000000 : ℝ)^3219
        have hw : |(6022790917/10000000000 : ℝ)|=(6022790917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199159637/2500000000 : ℝ)|^4243 ≤ (37969901692303/100000000000000 : ℝ)^3219
        have hw : |(1199159637/2500000000 : ℝ)|=(1199159637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s0_1 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2754214363/5000000000 : ℝ)*x 0 + (-2544529409/10000000000 : ℝ)*x 1 + (4796638511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2754214363/5000000000 : ℝ)^4243 ≤ (1423953390973/3125000000000 : ℝ)^3219 := by
    have hnat : (2754214363 : ℕ)^4243*3125000000000^3219 ≤ 1423953390973^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754214363 5000000000 1423953390973 3125000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544529409/10000000000 : ℝ)^4243 ≤ (16463590165373/100000000000000 : ℝ)^3219 := by
    have hnat : (2544529409 : ℕ)^4243*100000000000000^3219 ≤ 16463590165373^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544529409 10000000000 16463590165373 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4796638511/10000000000 : ℝ)^4243 ≤ (18984950653121/50000000000000 : ℝ)^3219 := by
    have hnat : (4796638511 : ℕ)^4243*50000000000000^3219 ≤ 18984950653121^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796638511 10000000000 18984950653121 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2754214363/5000000000 : ℝ), (-2544529409/10000000000 : ℝ), (4796638511/10000000000 : ℝ)] ![(1423953390973/3125000000000 : ℝ), (16463590165373/100000000000000 : ℝ), (18984950653121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2754214363/5000000000 : ℝ)|^4243 ≤ (1423953390973/3125000000000 : ℝ)^3219
        have hw : |(2754214363/5000000000 : ℝ)|=(2754214363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2544529409/10000000000 : ℝ)|^4243 ≤ (16463590165373/100000000000000 : ℝ)^3219
        have hw : |(-2544529409/10000000000 : ℝ)|=(2544529409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4796638511/10000000000 : ℝ)|^4243 ≤ (18984950653121/50000000000000 : ℝ)^3219
        have hw : |(4796638511/10000000000 : ℝ)|=(4796638511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s0_2 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1101685749/2000000000 : ℝ)*x 0 + (2398319261/5000000000 : ℝ)*x 1 + (-636132343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101685749/2000000000 : ℝ)^4243 ≤ (9113301743661/20000000000000 : ℝ)^3219 := by
    have hnat : (1101685749 : ℕ)^4243*20000000000000^3219 ≤ 9113301743661^3219*2000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101685749 2000000000 9113301743661 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2398319261/5000000000 : ℝ)^4243 ≤ (37969901421017/100000000000000 : ℝ)^3219 := by
    have hnat : (2398319261 : ℕ)^4243*100000000000000^3219 ≤ 37969901421017^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398319261 5000000000 37969901421017 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (636132343/2500000000 : ℝ)^4243 ≤ (16463589849821/100000000000000 : ℝ)^3219 := by
    have hnat : (636132343 : ℕ)^4243*100000000000000^3219 ≤ 16463589849821^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636132343 2500000000 16463589849821 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1101685749/2000000000 : ℝ), (2398319261/5000000000 : ℝ), (-636132343/2500000000 : ℝ)] ![(9113301743661/20000000000000 : ℝ), (37969901421017/100000000000000 : ℝ), (16463589849821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1101685749/2000000000 : ℝ)|^4243 ≤ (9113301743661/20000000000000 : ℝ)^3219
        have hw : |(1101685749/2000000000 : ℝ)|=(1101685749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2398319261/5000000000 : ℝ)|^4243 ≤ (37969901421017/100000000000000 : ℝ)^3219
        have hw : |(2398319261/5000000000 : ℝ)|=(2398319261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-636132343/2500000000 : ℝ)|^4243 ≤ (16463589849821/100000000000000 : ℝ)^3219
        have hw : |(-636132343/2500000000 : ℝ)|=(636132343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s0_3 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046929661/2500000000 : ℝ)*x 0 + (777508789/2500000000 : ℝ)*x 1 + (5621405383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046929661/2500000000 : ℝ)^4243 ≤ (31748579398641/100000000000000 : ℝ)^3219 := by
    have hnat : (1046929661 : ℕ)^4243*100000000000000^3219 ≤ 31748579398641^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046929661 2500000000 31748579398641 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777508789/2500000000 : ℝ)^4243 ≤ (10724529683769/50000000000000 : ℝ)^3219 := by
    have hnat : (777508789 : ℕ)^4243*50000000000000^3219 ≤ 10724529683769^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777508789 2500000000 10724529683769 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5621405383/10000000000 : ℝ)^4243 ≤ (46802361218813/100000000000000 : ℝ)^3219 := by
    have hnat : (5621405383 : ℕ)^4243*100000000000000^3219 ≤ 46802361218813^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5621405383 10000000000 46802361218813 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046929661/2500000000 : ℝ), (777508789/2500000000 : ℝ), (5621405383/10000000000 : ℝ)] ![(31748579398641/100000000000000 : ℝ), (10724529683769/50000000000000 : ℝ), (46802361218813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046929661/2500000000 : ℝ)|^4243 ≤ (31748579398641/100000000000000 : ℝ)^3219
        have hw : |(1046929661/2500000000 : ℝ)|=(1046929661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(777508789/2500000000 : ℝ)|^4243 ≤ (10724529683769/50000000000000 : ℝ)^3219
        have hw : |(777508789/2500000000 : ℝ)|=(777508789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5621405383/10000000000 : ℝ)|^4243 ≤ (46802361218813/100000000000000 : ℝ)^3219
        have hw : |(5621405383/10000000000 : ℝ)|=(5621405383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s0_4 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-924659547/5000000000 : ℝ)*x 0 + (4828298157/10000000000 : ℝ)*x 1 + (5990006073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (924659547/5000000000 : ℝ)^4243 ≤ (2162071738031/20000000000000 : ℝ)^3219 := by
    have hnat : (924659547 : ℕ)^4243*20000000000000^3219 ≤ 2162071738031^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924659547 5000000000 2162071738031 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4828298157/10000000000 : ℝ)^4243 ≤ (38300587148513/100000000000000 : ℝ)^3219 := by
    have hnat : (4828298157 : ℕ)^4243*100000000000000^3219 ≤ 38300587148513^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828298157 10000000000 38300587148513 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5990006073/10000000000 : ℝ)^4243 ≤ (25444527072631/50000000000000 : ℝ)^3219 := by
    have hnat : (5990006073 : ℕ)^4243*50000000000000^3219 ≤ 25444527072631^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5990006073 10000000000 25444527072631 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-924659547/5000000000 : ℝ), (4828298157/10000000000 : ℝ), (5990006073/10000000000 : ℝ)] ![(2162071738031/20000000000000 : ℝ), (38300587148513/100000000000000 : ℝ), (25444527072631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-924659547/5000000000 : ℝ)|^4243 ≤ (2162071738031/20000000000000 : ℝ)^3219
        have hw : |(-924659547/5000000000 : ℝ)|=(924659547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4828298157/10000000000 : ℝ)|^4243 ≤ (38300587148513/100000000000000 : ℝ)^3219
        have hw : |(4828298157/10000000000 : ℝ)|=(4828298157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5990006073/10000000000 : ℝ)|^4243 ≤ (25444527072631/50000000000000 : ℝ)^3219
        have hw : |(5990006073/10000000000 : ℝ)|=(5990006073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s0_5 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174686679/10000000000 : ℝ)*x 0 + (-675579687/5000000000 : ℝ)*x 1 + (5990008611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174686679/10000000000 : ℝ)^4243 ≤ (4196308119773/10000000000000 : ℝ)^3219 := by
    have hnat : (5174686679 : ℕ)^4243*10000000000000^3219 ≤ 4196308119773^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174686679 10000000000 4196308119773 10000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675579687/5000000000 : ℝ)^4243 ≤ (3573918106439/50000000000000 : ℝ)^3219 := by
    have hnat : (675579687 : ℕ)^4243*50000000000000^3219 ≤ 3573918106439^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675579687 5000000000 3573918106439 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5990008611/10000000000 : ℝ)^4243 ≤ (25444541283179/50000000000000 : ℝ)^3219 := by
    have hnat : (5990008611 : ℕ)^4243*50000000000000^3219 ≤ 25444541283179^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5990008611 10000000000 25444541283179 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174686679/10000000000 : ℝ), (-675579687/5000000000 : ℝ), (5990008611/10000000000 : ℝ)] ![(4196308119773/10000000000000 : ℝ), (3573918106439/50000000000000 : ℝ), (25444541283179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174686679/10000000000 : ℝ)|^4243 ≤ (4196308119773/10000000000000 : ℝ)^3219
        have hw : |(5174686679/10000000000 : ℝ)|=(5174686679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-675579687/5000000000 : ℝ)|^4243 ≤ (3573918106439/50000000000000 : ℝ)^3219
        have hw : |(-675579687/5000000000 : ℝ)|=(675579687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5990008611/10000000000 : ℝ)|^4243 ≤ (25444541283179/50000000000000 : ℝ)^3219
        have hw : |(5990008611/10000000000 : ℝ)|=(5990008611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s0_6 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174687907/10000000000 : ℝ)*x 0 + (599000649/1000000000 : ℝ)*x 1 + (-675580449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174687907/10000000000 : ℝ)^4243 ≤ (41963094323771/100000000000000 : ℝ)^3219 := by
    have hnat : (5174687907 : ℕ)^4243*100000000000000^3219 ≤ 41963094323771^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174687907 10000000000 41963094323771 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (599000649/1000000000 : ℝ)^4243 ≤ (25444529407461/50000000000000 : ℝ)^3219 := by
    have hnat : (599000649 : ℕ)^4243*50000000000000^3219 ≤ 25444529407461^3219*1000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599000649 1000000000 25444529407461 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675580449/5000000000 : ℝ)^4243 ≤ (3573923419871/50000000000000 : ℝ)^3219 := by
    have hnat : (675580449 : ℕ)^4243*50000000000000^3219 ≤ 3573923419871^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675580449 5000000000 3573923419871 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174687907/10000000000 : ℝ), (599000649/1000000000 : ℝ), (-675580449/5000000000 : ℝ)] ![(41963094323771/100000000000000 : ℝ), (25444529407461/50000000000000 : ℝ), (3573923419871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174687907/10000000000 : ℝ)|^4243 ≤ (41963094323771/100000000000000 : ℝ)^3219
        have hw : |(5174687907/10000000000 : ℝ)|=(5174687907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(599000649/1000000000 : ℝ)|^4243 ≤ (25444529407461/50000000000000 : ℝ)^3219
        have hw : |(599000649/1000000000 : ℝ)|=(599000649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-675580449/5000000000 : ℝ)|^4243 ≤ (3573923419871/50000000000000 : ℝ)^3219
        have hw : |(-675580449/5000000000 : ℝ)|=(675580449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s0_7 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2098749961/5000000000 : ℝ)*x 0 + (138914197/250000000 : ℝ)*x 1 + (158858873/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098749961/5000000000 : ℝ)^4243 ≤ (31846360671739/100000000000000 : ℝ)^3219 := by
    have hnat : (2098749961 : ℕ)^4243*100000000000000^3219 ≤ 31846360671739^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098749961 5000000000 31846360671739 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138914197/250000000 : ℝ)^4243 ≤ (46092126948409/100000000000000 : ℝ)^3219 := by
    have hnat : (138914197 : ℕ)^4243*100000000000000^3219 ≤ 46092126948409^3219*250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138914197 250000000 46092126948409 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158858873/500000000 : ℝ)^4243 ≤ (5515378090831/25000000000000 : ℝ)^3219 := by
    have hnat : (158858873 : ℕ)^4243*25000000000000^3219 ≤ 5515378090831^3219*500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158858873 500000000 5515378090831 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098749961/5000000000 : ℝ), (138914197/250000000 : ℝ), (158858873/500000000 : ℝ)] ![(31846360671739/100000000000000 : ℝ), (46092126948409/100000000000000 : ℝ), (5515378090831/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098749961/5000000000 : ℝ)|^4243 ≤ (31846360671739/100000000000000 : ℝ)^3219
        have hw : |(2098749961/5000000000 : ℝ)|=(2098749961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138914197/250000000 : ℝ)|^4243 ≤ (46092126948409/100000000000000 : ℝ)^3219
        have hw : |(138914197/250000000 : ℝ)|=(138914197/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158858873/500000000 : ℝ)|^4243 ≤ (5515378090831/25000000000000 : ℝ)^3219
        have hw : |(158858873/500000000 : ℝ)|=(158858873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1283_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (481/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13651/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2121/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2121 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2121*1^512 ≤ 0^512*1^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2121/512 : ℝ) ≤ (1123239659922427859/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2121 ≤ (1123239659922427859/50000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2121*50000000000000000000^512 ≤ 1123239659922427859^512*5^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1123239659922427859 50000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1123239659922427859/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2121 := by
      have hnat : (1 : ℕ)^512*1^2121 ≤ 1^2121*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (51123239659922427859/50000000000000000000 : ℝ) ≤ (5026886462536597/5000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (51123239659922427859/50000000000000000000 : ℝ)^512 ≤ (5026886462536597/5000000000000000 : ℝ)^2121 := by
      have hnat : (51123239659922427859 : ℕ)^512*5000000000000000^2121 ≤ 5026886462536597^2121*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51123239659922427859 50000000000000000000 5026886462536597 5000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026886462536597/5000000000000000 : ℝ)) (X := (51123239659922427859/50000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (26123239659922427859/25000000000000000000 : ℝ) ≤ (2526886462536597/2500000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (26123239659922427859/25000000000000000000 : ℝ)^512 ≤ (2526886462536597/2500000000000000 : ℝ)^2121 := by
      have hnat : (26123239659922427859 : ℕ)^512*2500000000000000^2121 ≤ 2526886462536597^2121*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26123239659922427859 25000000000000000000 2526886462536597 2500000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2526886462536597/2500000000000000 : ℝ)) (X := (26123239659922427859/25000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26886462536597/2000000000000000 : ℝ)*(0 : ℝ))^(2121/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(26886462536597/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1123239659922427859/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26886462536597/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2121/512 : ℝ) := by
    rw [show (1 : ℝ)+(26886462536597/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5026886462536597/5000000000000000 : ℝ) by norm_num, show 1+(1123239659922427859/50000000000000000000 : ℝ)+(0 : ℝ)=(51123239659922427859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1123239659922427859/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26886462536597/2000000000000000 : ℝ)*(2/5 : ℝ))^(2121/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(26886462536597/2000000000000000 : ℝ)*(2/5 : ℝ)=(2526886462536597/2500000000000000 : ℝ) by norm_num, show 1+2*(1123239659922427859/50000000000000000000 : ℝ)=(26123239659922427859/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26886462536597/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26886462536597/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26886462536597/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26886462536597/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26886462536597/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26886462536597/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1801314/9765625 : ℝ)*X 0 0+(6022790917/10000000000 : ℝ)*X 0 1+(1199159637/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2754214363/5000000000 : ℝ)*X 1 0+(-2544529409/10000000000 : ℝ)*X 1 1+(4796638511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1101685749/2000000000 : ℝ)*X 2 0+(2398319261/5000000000 : ℝ)*X 2 1+(-636132343/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1046929661/2500000000 : ℝ)*X 0 0+(777508789/2500000000 : ℝ)*X 0 1+(5621405383/10000000000 : ℝ)*X 0 2+(1046929661/2500000000 : ℝ)*X 1 0+(777508789/2500000000 : ℝ)*X 1 1+(5621405383/10000000000 : ℝ)*X 1 2+(1046929661/2500000000 : ℝ)*X 2 0+(777508789/2500000000 : ℝ)*X 2 1+(5621405383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-924659547/5000000000 : ℝ)*X 0 0+(4828298157/10000000000 : ℝ)*X 0 1+(5990006073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174686679/10000000000 : ℝ)*X 1 0+(-675579687/5000000000 : ℝ)*X 1 1+(5990008611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174687907/10000000000 : ℝ)*X 2 0+(599000649/1000000000 : ℝ)*X 2 1+(-675580449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2098749961/5000000000 : ℝ)*X 0 0+(138914197/250000000 : ℝ)*X 0 1+(158858873/500000000 : ℝ)*X 0 2+(2098749961/5000000000 : ℝ)*X 1 0+(138914197/250000000 : ℝ)*X 1 1+(158858873/500000000 : ℝ)*X 1 2+(2098749961/5000000000 : ℝ)*X 2 0+(138914197/250000000 : ℝ)*X 2 1+(158858873/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (142333931486150782790103/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33734663/50000000000000 : ℝ)*(base1) + (2159993/156250000000 : ℝ)*(base19) + (1385208621/100000000000000 : ℝ)*(base23) + (156752491/100000000000000 : ℝ)*(upper3) + (166909621/100000000000000 : ℝ)*(upper5) + (303440296062967/50000000000000 : ℝ)*(major0) + (303440296062967/50000000000000 : ℝ)*(major1) + (303440296062967/50000000000000 : ℝ)*(major2) + (203890862024649/25000000000000 : ℝ)*(sp0) + (815566415797173/100000000000000 : ℝ)*(sp1) + (815566412984073/100000000000000 : ℝ)*(sp2) + (15927640878809/4000000000000 : ℝ)*(sp3) + (4417563423/100000000000000 : ℝ)*(sp4) + (2106841043/100000000000000 : ℝ)*(sp7) + (199096598140297/50000000000000 : ℝ)*(f.failure) + (407783899096347/50000000000000 : ℝ)*(f.sum) + (58336112496701/50000000000000000000000000000 : ℝ)*base66 + (809849965603299/100000000000000000000000000000 : ℝ)*base67 + (42983409703299/100000000000000000000000000000 : ℝ)*base69 + (219692739503299/100000000000000000000000000000 : ℝ)*base71 + (11540844753299/50000000000000000000000000000 : ℝ)*base73 + (616405118103299/100000000000000000000000000000 : ℝ)*base75 + (119934060803299/100000000000000000000000000000 : ℝ)*base77 + (118500349303299/100000000000000000000000000000 : ℝ)*base79 + (224926736046701/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (8407963/5000000000000000000000 : ℝ)*base89 + (8407963/5000000000000000000000 : ℝ)*base91 + (8407963/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3313858046981995665447/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23130283/6250000000000 : ℝ)*(base1) + (80940373/6250000000000 : ℝ)*(base19) + (742618617/50000000000000 : ℝ)*(base23) + (33266197/12500000000000 : ℝ)*(upper3) + (3202692563339/500000000000 : ℝ)*(major0) + (3202692563339/500000000000 : ℝ)*(major1) + (3202692563339/500000000000 : ℝ)*(major2) + (2094679791/100000000000000 : ℝ)*(sp1) + (938157357/50000000000000 : ℝ)*(sp2) + (164091033/100000000000000 : ℝ)*(sp3) + (43039998584177/5000000000000 : ℝ)*(sp4) + (430398105936627/50000000000000 : ℝ)*(sp5) + (172159248009413/20000000000000 : ℝ)*(sp6) + (8405533372743/2000000000000 : ℝ)*(sp7) + (420277202812711/100000000000000 : ℝ)*(f.failure) + (860799601599013/100000000000000 : ℝ)*(f.sum) + (827526378617/500000000000000000000000000 : ℝ)*base66 + (5010305910617/1000000000000000000000000000 : ℝ)*base68 + (1097019958383/1000000000000000000000000000 : ℝ)*base69 + (4966853266617/1000000000000000000000000000 : ℝ)*base72 + (461792799117/500000000000000000000000000 : ℝ)*base74 + (11893463016617/1000000000000000000000000000 : ℝ)*base76 + (4970990419617/1000000000000000000000000000 : ℝ)*base78 + (10464334688617/1000000000000000000000000000 : ℝ)*base80 + (1182815186883/500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (86647669/10000000000000000000000 : ℝ)*base89 + (86647669/10000000000000000000000 : ℝ)*base91 + (86647669/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1283_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (481/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13651/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1283_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1283_s1_0 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-127368203/625000000 : ℝ)*x 0 + (1133930271/2000000000 : ℝ)*x 1 + (5025999323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127368203/625000000 : ℝ)^4243 ≤ (12286374087639/100000000000000 : ℝ)^3219 := by
    have hnat : (127368203 : ℕ)^4243*100000000000000^3219 ≤ 12286374087639^3219*625000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127368203 625000000 12286374087639 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133930271/2000000000 : ℝ)^4243 ≤ (47332546022497/100000000000000 : ℝ)^3219 := by
    have hnat : (1133930271 : ℕ)^4243*100000000000000^3219 ≤ 47332546022497^3219*2000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133930271 2000000000 47332546022497 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5025999323/10000000000 : ℝ)^4243 ≤ (20190539937043/50000000000000 : ℝ)^3219 := by
    have hnat : (5025999323 : ℕ)^4243*50000000000000^3219 ≤ 20190539937043^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025999323 10000000000 20190539937043 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127368203/625000000 : ℝ), (1133930271/2000000000 : ℝ), (5025999323/10000000000 : ℝ)] ![(12286374087639/100000000000000 : ℝ), (47332546022497/100000000000000 : ℝ), (20190539937043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127368203/625000000 : ℝ)|^4243 ≤ (12286374087639/100000000000000 : ℝ)^3219
        have hw : |(-127368203/625000000 : ℝ)|=(127368203/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133930271/2000000000 : ℝ)|^4243 ≤ (47332546022497/100000000000000 : ℝ)^3219
        have hw : |(1133930271/2000000000 : ℝ)|=(1133930271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5025999323/10000000000 : ℝ)|^4243 ≤ (20190539937043/50000000000000 : ℝ)^3219
        have hw : |(5025999323/10000000000 : ℝ)|=(5025999323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s1_1 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1352986329/2500000000 : ℝ)*x 0 + (-1191582241/5000000000 : ℝ)*x 1 + (628249897/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352986329/2500000000 : ℝ)^4243 ≤ (1780697369387/4000000000000 : ℝ)^3219 := by
    have hnat : (1352986329 : ℕ)^4243*4000000000000^3219 ≤ 1780697369387^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352986329 2500000000 1780697369387 4000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1191582241/5000000000 : ℝ)^4243 ≤ (3775371858973/25000000000000 : ℝ)^3219 := by
    have hnat : (1191582241 : ℕ)^4243*25000000000000^3219 ≤ 3775371858973^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191582241 5000000000 3775371858973 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628249897/1250000000 : ℝ)^4243 ≤ (8076215663463/20000000000000 : ℝ)^3219 := by
    have hnat : (628249897 : ℕ)^4243*20000000000000^3219 ≤ 8076215663463^3219*1250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628249897 1250000000 8076215663463 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352986329/2500000000 : ℝ), (-1191582241/5000000000 : ℝ), (628249897/1250000000 : ℝ)] ![(1780697369387/4000000000000 : ℝ), (3775371858973/25000000000000 : ℝ), (8076215663463/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352986329/2500000000 : ℝ)|^4243 ≤ (1780697369387/4000000000000 : ℝ)^3219
        have hw : |(1352986329/2500000000 : ℝ)|=(1352986329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1191582241/5000000000 : ℝ)|^4243 ≤ (3775371858973/25000000000000 : ℝ)^3219
        have hw : |(-1191582241/5000000000 : ℝ)|=(1191582241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628249897/1250000000 : ℝ)|^4243 ≤ (8076215663463/20000000000000 : ℝ)^3219
        have hw : |(628249897/1250000000 : ℝ)|=(628249897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s1_2 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5411945109/10000000000 : ℝ)*x 0 + (5025999333/10000000000 : ℝ)*x 1 + (-2383164551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411945109/10000000000 : ℝ)^4243 ≤ (44517431990281/100000000000000 : ℝ)^3219 := by
    have hnat : (5411945109 : ℕ)^4243*100000000000000^3219 ≤ 44517431990281^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411945109 10000000000 44517431990281 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5025999333/10000000000 : ℝ)^4243 ≤ (40381079979989/100000000000000 : ℝ)^3219 := by
    have hnat : (5025999333 : ℕ)^4243*100000000000000^3219 ≤ 40381079979989^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025999333 10000000000 40381079979989 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2383164551/10000000000 : ℝ)^4243 ≤ (1887686001527/12500000000000 : ℝ)^3219 := by
    have hnat : (2383164551 : ℕ)^4243*12500000000000^3219 ≤ 1887686001527^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383164551 10000000000 1887686001527 12500000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411945109/10000000000 : ℝ), (5025999333/10000000000 : ℝ), (-2383164551/10000000000 : ℝ)] ![(44517431990281/100000000000000 : ℝ), (40381079979989/100000000000000 : ℝ), (1887686001527/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411945109/10000000000 : ℝ)|^4243 ≤ (44517431990281/100000000000000 : ℝ)^3219
        have hw : |(5411945109/10000000000 : ℝ)|=(5411945109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5025999333/10000000000 : ℝ)|^4243 ≤ (40381079979989/100000000000000 : ℝ)^3219
        have hw : |(5025999333/10000000000 : ℝ)|=(5025999333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2383164551/10000000000 : ℝ)|^4243 ≤ (1887686001527/12500000000000 : ℝ)^3219
        have hw : |(-2383164551/10000000000 : ℝ)|=(2383164551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s1_3 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4302712077/10000000000 : ℝ)*x 0 + (3691581229/10000000000 : ℝ)*x 1 + (1252472717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302712077/10000000000 : ℝ)^4243 ≤ (8225676163417/25000000000000 : ℝ)^3219 := by
    have hnat : (4302712077 : ℕ)^4243*25000000000000^3219 ≤ 8225676163417^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302712077 10000000000 8225676163417 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3691581229/10000000000 : ℝ)^4243 ≤ (26886721528173/100000000000000 : ℝ)^3219 := by
    have hnat : (3691581229 : ℕ)^4243*100000000000000^3219 ≤ 26886721528173^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3691581229 10000000000 26886721528173 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252472717/2500000000 : ℝ)^4243 ≤ (10052643451973/25000000000000 : ℝ)^3219 := by
    have hnat : (1252472717 : ℕ)^4243*25000000000000^3219 ≤ 10052643451973^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252472717 2500000000 10052643451973 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302712077/10000000000 : ℝ), (3691581229/10000000000 : ℝ), (1252472717/2500000000 : ℝ)] ![(8225676163417/25000000000000 : ℝ), (26886721528173/100000000000000 : ℝ), (10052643451973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302712077/10000000000 : ℝ)|^4243 ≤ (8225676163417/25000000000000 : ℝ)^3219
        have hw : |(4302712077/10000000000 : ℝ)|=(4302712077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3691581229/10000000000 : ℝ)|^4243 ≤ (26886721528173/100000000000000 : ℝ)^3219
        have hw : |(3691581229/10000000000 : ℝ)|=(3691581229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252472717/2500000000 : ℝ)|^4243 ≤ (10052643451973/25000000000000 : ℝ)^3219
        have hw : |(1252472717/2500000000 : ℝ)|=(1252472717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s1_4 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1019274081/5000000000 : ℝ)*x 0 + (62930609/125000000 : ℝ)*x 1 + (2830520521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019274081/5000000000 : ℝ)^4243 ≤ (12291594749529/100000000000000 : ℝ)^3219 := by
    have hnat : (1019274081 : ℕ)^4243*100000000000000^3219 ≤ 12291594749529^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019274081 5000000000 12291594749529 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62930609/125000000 : ℝ)^4243 ≤ (2023529264781/5000000000000 : ℝ)^3219 := by
    have hnat : (62930609 : ℕ)^4243*5000000000000^3219 ≤ 2023529264781^3219*125000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62930609 125000000 2023529264781 5000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2830520521/5000000000 : ℝ)^4243 ≤ (47237819945303/100000000000000 : ℝ)^3219 := by
    have hnat : (2830520521 : ℕ)^4243*100000000000000^3219 ≤ 47237819945303^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2830520521 5000000000 47237819945303 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1019274081/5000000000 : ℝ), (62930609/125000000 : ℝ), (2830520521/5000000000 : ℝ)] ![(12291594749529/100000000000000 : ℝ), (2023529264781/5000000000000 : ℝ), (47237819945303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1019274081/5000000000 : ℝ)|^4243 ≤ (12291594749529/100000000000000 : ℝ)^3219
        have hw : |(-1019274081/5000000000 : ℝ)|=(1019274081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(62930609/125000000 : ℝ)|^4243 ≤ (2023529264781/5000000000000 : ℝ)^3219
        have hw : |(62930609/125000000 : ℝ)|=(62930609/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2830520521/5000000000 : ℝ)|^4243 ≤ (47237819945303/100000000000000 : ℝ)^3219
        have hw : |(2830520521/5000000000 : ℝ)|=(2830520521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s1_5 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5245782471/10000000000 : ℝ)*x 0 + (-1748122491/10000000000 : ℝ)*x 1 + (226441661/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245782471/10000000000 : ℝ)^4243 ≤ (21362338327651/50000000000000 : ℝ)^3219 := by
    have hnat : (5245782471 : ℕ)^4243*50000000000000^3219 ≤ 21362338327651^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245782471 10000000000 21362338327651 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1748122491/10000000000 : ℝ)^4243 ≤ (5018749036177/50000000000000 : ℝ)^3219 := by
    have hnat : (1748122491 : ℕ)^4243*50000000000000^3219 ≤ 5018749036177^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748122491 10000000000 5018749036177 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226441661/400000000 : ℝ)^4243 ≤ (47237825257727/100000000000000 : ℝ)^3219 := by
    have hnat : (226441661 : ℕ)^4243*100000000000000^3219 ≤ 47237825257727^3219*400000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226441661 400000000 47237825257727 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245782471/10000000000 : ℝ), (-1748122491/10000000000 : ℝ), (226441661/400000000 : ℝ)] ![(21362338327651/50000000000000 : ℝ), (5018749036177/50000000000000 : ℝ), (47237825257727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245782471/10000000000 : ℝ)|^4243 ≤ (21362338327651/50000000000000 : ℝ)^3219
        have hw : |(5245782471/10000000000 : ℝ)|=(5245782471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1748122491/10000000000 : ℝ)|^4243 ≤ (5018749036177/50000000000000 : ℝ)^3219
        have hw : |(-1748122491/10000000000 : ℝ)|=(1748122491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226441661/400000000 : ℝ)|^4243 ≤ (47237825257727/100000000000000 : ℝ)^3219
        have hw : |(226441661/400000000 : ℝ)|=(226441661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s1_6 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5245782379/10000000000 : ℝ)*x 0 + (1415260299/2500000000 : ℝ)*x 1 + (-1748123099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245782379/10000000000 : ℝ)^4243 ≤ (1068116891691/2500000000000 : ℝ)^3219 := by
    have hnat : (5245782379 : ℕ)^4243*2500000000000^3219 ≤ 1068116891691^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245782379 10000000000 1068116891691 2500000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1415260299/2500000000 : ℝ)^4243 ≤ (47237821639119/100000000000000 : ℝ)^3219 := by
    have hnat : (1415260299 : ℕ)^4243*100000000000000^3219 ≤ 47237821639119^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415260299 2500000000 47237821639119 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1748123099/10000000000 : ℝ)^4243 ≤ (5018751336979/50000000000000 : ℝ)^3219 := by
    have hnat : (1748123099 : ℕ)^4243*50000000000000^3219 ≤ 5018751336979^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748123099 10000000000 5018751336979 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245782379/10000000000 : ℝ), (1415260299/2500000000 : ℝ), (-1748123099/10000000000 : ℝ)] ![(1068116891691/2500000000000 : ℝ), (47237821639119/100000000000000 : ℝ), (5018751336979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245782379/10000000000 : ℝ)|^4243 ≤ (1068116891691/2500000000000 : ℝ)^3219
        have hw : |(5245782379/10000000000 : ℝ)|=(5245782379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1415260299/2500000000 : ℝ)|^4243 ≤ (47237821639119/100000000000000 : ℝ)^3219
        have hw : |(1415260299/2500000000 : ℝ)|=(1415260299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1748123099/10000000000 : ℝ)|^4243 ≤ (5018751336979/50000000000000 : ℝ)^3219
        have hw : |(-1748123099/10000000000 : ℝ)|=(1748123099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s1_7 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4304057037/10000000000 : ℝ)*x 0 + (199703411/400000000 : ℝ)*x 1 + (3709216143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304057037/10000000000 : ℝ)^4243 ≤ (16458130963113/50000000000000 : ℝ)^3219 := by
    have hnat : (4304057037 : ℕ)^4243*50000000000000^3219 ≤ 16458130963113^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304057037 10000000000 16458130963113 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199703411/400000000 : ℝ)^4243 ≤ (2001379520651/5000000000000 : ℝ)^3219 := by
    have hnat : (199703411 : ℕ)^4243*5000000000000^3219 ≤ 2001379520651^3219*400000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199703411 400000000 2001379520651 5000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3709216143/10000000000 : ℝ)^4243 ≤ (13528073815977/50000000000000 : ℝ)^3219 := by
    have hnat : (3709216143 : ℕ)^4243*50000000000000^3219 ≤ 13528073815977^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3709216143 10000000000 13528073815977 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304057037/10000000000 : ℝ), (199703411/400000000 : ℝ), (3709216143/10000000000 : ℝ)] ![(16458130963113/50000000000000 : ℝ), (2001379520651/5000000000000 : ℝ), (13528073815977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304057037/10000000000 : ℝ)|^4243 ≤ (16458130963113/50000000000000 : ℝ)^3219
        have hw : |(4304057037/10000000000 : ℝ)|=(4304057037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(199703411/400000000 : ℝ)|^4243 ≤ (2001379520651/5000000000000 : ℝ)^3219
        have hw : |(199703411/400000000 : ℝ)|=(199703411/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3709216143/10000000000 : ℝ)|^4243 ≤ (13528073815977/50000000000000 : ℝ)^3219
        have hw : |(3709216143/10000000000 : ℝ)|=(3709216143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1283_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13651/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (481/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3159/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19923/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13651/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (481/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13651/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (481/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13651/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (481/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13651/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (481/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13651/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (481/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13651/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (481/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (481/50000 : ℝ) ^ (2121/512 : ℝ) ≤ (44171807563/10000000000000000000 : ℝ) := by
    have hpowers : (481/50000 : ℝ)^2121 ≤ (44171807563/10000000000000000000 : ℝ)^512 := by
      have hnat : (481 : ℕ)^2121*10000000000000000000^512 ≤ 44171807563^512*50000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        481 50000 44171807563 10000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (481/50000 : ℝ)) (X := (44171807563/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13651/50000 : ℝ) ^ (2121/512 : ℝ) ≤ (461733636019889111/100000000000000000000 : ℝ) := by
    have hpowers : (13651/50000 : ℝ)^2121 ≤ (461733636019889111/100000000000000000000 : ℝ)^512 := by
      have hnat : (13651 : ℕ)^2121*100000000000000000000^512 ≤ 461733636019889111^512*50000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13651 50000 461733636019889111 100000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13651/50000 : ℝ)) (X := (461733636019889111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000044171807563/5000000000000000000 : ℝ) ≤ (5000000010662879/5000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (5000000044171807563/5000000000000000000 : ℝ)^512 ≤ (5000000010662879/5000000000000000 : ℝ)^2121 := by
      have hnat : (5000000044171807563 : ℕ)^512*5000000000000000^2121 ≤ 5000000010662879^2121*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000044171807563 5000000000000000000 5000000010662879 5000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000010662879/5000000000000000 : ℝ)) (X := (5000000044171807563/5000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100461734077737964741/100000000000000000000 : ℝ) ≤ (2002225317565997/2000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (100461734077737964741/100000000000000000000 : ℝ)^512 ≤ (2002225317565997/2000000000000000 : ℝ)^2121 := by
      have hnat : (100461734077737964741 : ℕ)^512*2000000000000000^2121 ≤ 2002225317565997^2121*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100461734077737964741 100000000000000000000 2002225317565997 2000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002225317565997/2000000000000000 : ℝ)) (X := (100461734077737964741/100000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50461733636019889111/50000000000000000000 : ℝ) ≤ (2505563288583553/2500000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (50461733636019889111/50000000000000000000 : ℝ)^512 ≤ (2505563288583553/2500000000000000 : ℝ)^2121 := by
      have hnat : (50461733636019889111 : ℕ)^512*2500000000000000^2121 ≤ 2505563288583553^2121*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50461733636019889111 50000000000000000000 2505563288583553 2500000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505563288583553/2500000000000000 : ℝ)) (X := (50461733636019889111/50000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(44171807563/10000000000000000000 : ℝ) ≤ ((21948216087313861081/21950000000000000000 : ℝ)+2*(3708855501409/878000000000000 : ℝ)*(481/50000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (21948216087313861081/21950000000000000000 : ℝ)+2*(3708855501409/878000000000000 : ℝ)*(481/50000 : ℝ)=(5000000010662879/5000000000000000 : ℝ) by norm_num, show 1+2*(44171807563/10000000000000000000 : ℝ)=(5000000044171807563/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(461733636019889111/100000000000000000000 : ℝ)+(44171807563/10000000000000000000 : ℝ) ≤ ((21948216087313861081/21950000000000000000 : ℝ)+(3708855501409/878000000000000 : ℝ)*((13651/50000 : ℝ)+(481/50000 : ℝ)))^(2121/512 : ℝ) := by
    rw [show (21948216087313861081/21950000000000000000 : ℝ)+(3708855501409/878000000000000 : ℝ)*((13651/50000 : ℝ)+(481/50000 : ℝ))=(2002225317565997/2000000000000000 : ℝ) by norm_num, show 1+(461733636019889111/100000000000000000000 : ℝ)+(44171807563/10000000000000000000 : ℝ)=(100461734077737964741/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(461733636019889111/100000000000000000000 : ℝ) ≤ ((21948216087313861081/21950000000000000000 : ℝ)+2*(3708855501409/878000000000000 : ℝ)*(13651/50000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (21948216087313861081/21950000000000000000 : ℝ)+2*(3708855501409/878000000000000 : ℝ)*(13651/50000 : ℝ)=(2505563288583553/2500000000000000 : ℝ) by norm_num, show 1+2*(461733636019889111/100000000000000000000 : ℝ)=(50461733636019889111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21948216087313861081/21950000000000000000 : ℝ)*(X 1 0+X 2 0)+(3708855501409/878000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (481/50000 : ℝ)) (hi := (13651/50000 : ℝ)) (c := (21948216087313861081/21950000000000000000 : ℝ)) (alpha := (3708855501409/878000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21948216087313861081/21950000000000000000 : ℝ)*(X 0 1+X 2 1)+(3708855501409/878000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (481/50000 : ℝ)) (hi := (13651/50000 : ℝ)) (c := (21948216087313861081/21950000000000000000 : ℝ)) (alpha := (3708855501409/878000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21948216087313861081/21950000000000000000 : ℝ)*(X 0 2+X 1 2)+(3708855501409/878000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (481/50000 : ℝ)) (hi := (13651/50000 : ℝ)) (c := (21948216087313861081/21950000000000000000 : ℝ)) (alpha := (3708855501409/878000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-127368203/625000000 : ℝ)*X 0 0+(1133930271/2000000000 : ℝ)*X 0 1+(5025999323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1352986329/2500000000 : ℝ)*X 1 0+(-1191582241/5000000000 : ℝ)*X 1 1+(628249897/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5411945109/10000000000 : ℝ)*X 2 0+(5025999333/10000000000 : ℝ)*X 2 1+(-2383164551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302712077/10000000000 : ℝ)*X 0 0+(3691581229/10000000000 : ℝ)*X 0 1+(1252472717/2500000000 : ℝ)*X 0 2+(4302712077/10000000000 : ℝ)*X 1 0+(3691581229/10000000000 : ℝ)*X 1 1+(1252472717/2500000000 : ℝ)*X 1 2+(4302712077/10000000000 : ℝ)*X 2 0+(3691581229/10000000000 : ℝ)*X 2 1+(1252472717/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1019274081/5000000000 : ℝ)*X 0 0+(62930609/125000000 : ℝ)*X 0 1+(2830520521/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5245782471/10000000000 : ℝ)*X 1 0+(-1748122491/10000000000 : ℝ)*X 1 1+(226441661/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5245782379/10000000000 : ℝ)*X 2 0+(1415260299/2500000000 : ℝ)*X 2 1+(-1748123099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4304057037/10000000000 : ℝ)*X 0 0+(199703411/400000000 : ℝ)*X 0 1+(3709216143/10000000000 : ℝ)*X 0 2+(4304057037/10000000000 : ℝ)*X 1 0+(199703411/400000000 : ℝ)*X 1 1+(3709216143/10000000000 : ℝ)*X 1 2+(4304057037/10000000000 : ℝ)*X 2 0+(199703411/400000000 : ℝ)*X 2 1+(3709216143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (146037597708268615263733719/17148437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (91451173/100000000000000 : ℝ)*(base1) + (439271307/25000000000000 : ℝ)*(base19) + (1697660027/100000000000000 : ℝ)*(base23) + (206173147/100000000000000 : ℝ)*(upper3) + (164840557/100000000000000 : ℝ)*(upper5) + (36128286944491/3125000000000 : ℝ)*(major0) + (36128286944491/3125000000000 : ℝ)*(major1) + (36128286944491/3125000000000 : ℝ)*(major2) + (776822119906803/50000000000000 : ℝ)*(sp0) + (31073036474293/2000000000000 : ℝ)*(sp1) + (1553651883139851/100000000000000 : ℝ)*(sp2) + (758551646276043/100000000000000 : ℝ)*(sp3) + (1886487489/20000000000000 : ℝ)*(sp4) + (2381025367/50000000000000 : ℝ)*(sp7) + (758556499777951/100000000000000 : ℝ)*(f.failure) + (776826790399939/50000000000000 : ℝ)*(f.sum) + (1037395196173/10975000000000000000000000000 : ℝ)*base66 + (302849252725698521/68593750000000000000000000000000 : ℝ)*base67 + (21252326351792271/68593750000000000000000000000000 : ℝ)*base69 + (322373905373988979/68593750000000000000000000000000 : ℝ)*base72 + (50903577870477/10975000000000000000000000000 : ℝ)*base73 + (151214446415082729/68593750000000000000000000000000 : ℝ)*base76 + (212236992655395229/68593750000000000000000000000000 : ℝ)*base78 + (205160371097270229/68593750000000000000000000000000 : ℝ)*base80 + (44180567377177/10975000000000000000000000000 : ℝ)*base81 + (127441629/10000000000000000000000 : ℝ)*base89 + (127441629/10000000000000000000000 : ℝ)*base91 + (127441629/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1238657893000617216704429787/274375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (794071333/100000000000000 : ℝ)*(base19) + (745229201/100000000000000 : ℝ)*(base23) + (1829147/20000000000000 : ℝ)*(upper2) + (134852933/100000000000000 : ℝ)*(upper3) + (19199549/20000000000000 : ℝ)*(upper5) + (593783154463291/50000000000000 : ℝ)*(major0) + (593783154463291/50000000000000 : ℝ)*(major1) + (593783154463291/50000000000000 : ℝ)*(major2) + (4515839013/100000000000000 : ℝ)*(sp1) + (826776729/25000000000000 : ℝ)*(sp2) + (1595933345694989/100000000000000 : ℝ)*(sp4) + (398982008946161/25000000000000 : ℝ)*(sp5) + (1595929293358871/100000000000000 : ℝ)*(sp6) + (779199121675809/100000000000000 : ℝ)*(sp7) + (779199121675809/100000000000000 : ℝ)*(f.failure) + (1595933345694989/100000000000000 : ℝ)*(f.sum) + (67388152567231/21950000000000000000000000000 : ℝ)*base66 + (11538492218301052571/1097500000000000000000000000000000 : ℝ)*base67 + (4455066247976052571/1097500000000000000000000000000000 : ℝ)*base69 + (4343578751826052571/1097500000000000000000000000000000 : ℝ)*base71 + (117075470567269/21950000000000000000000000000 : ℝ)*base73 + (3430753144898947429/1097500000000000000000000000000000 : ℝ)*base76 + (8997176827528552571/1097500000000000000000000000000000 : ℝ)*base77 + (14790085469561052571/1097500000000000000000000000000000 : ℝ)*base79 + (49060583609881/21950000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (51634589/10000000000000000000000 : ℝ)*base90 + (51634589/10000000000000000000000 : ℝ)*base92 + (51634589/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1283_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13651/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (481/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3159/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19923/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1283_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1283_s2_0 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-65107693/312500000 : ℝ)*x 0 + (5497049287/10000000000 : ℝ)*x 1 + (2584759591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65107693/312500000 : ℝ)^4243 ≤ (12649672758709/100000000000000 : ℝ)^3219 := by
    have hnat : (65107693 : ℕ)^4243*100000000000000^3219 ≤ 12649672758709^3219*312500000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65107693 312500000 12649672758709 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497049287/10000000000 : ℝ)^4243 ≤ (45442472402169/100000000000000 : ℝ)^3219 := by
    have hnat : (5497049287 : ℕ)^4243*100000000000000^3219 ≤ 45442472402169^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497049287 10000000000 45442472402169 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2584759591/5000000000 : ℝ)^4243 ≤ (1676314192609/4000000000000 : ℝ)^3219 := by
    have hnat : (2584759591 : ℕ)^4243*4000000000000^3219 ≤ 1676314192609^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584759591 5000000000 1676314192609 4000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65107693/312500000 : ℝ), (5497049287/10000000000 : ℝ), (2584759591/5000000000 : ℝ)] ![(12649672758709/100000000000000 : ℝ), (45442472402169/100000000000000 : ℝ), (1676314192609/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65107693/312500000 : ℝ)|^4243 ≤ (12649672758709/100000000000000 : ℝ)^3219
        have hw : |(-65107693/312500000 : ℝ)|=(65107693/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497049287/10000000000 : ℝ)|^4243 ≤ (45442472402169/100000000000000 : ℝ)^3219
        have hw : |(5497049287/10000000000 : ℝ)|=(5497049287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2584759591/5000000000 : ℝ)|^4243 ≤ (1676314192609/4000000000000 : ℝ)^3219
        have hw : |(2584759591/5000000000 : ℝ)|=(2584759591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s2_1 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074052369/2000000000 : ℝ)*x 0 + (-2253274403/10000000000 : ℝ)*x 1 + (5169519829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074052369/2000000000 : ℝ)^4243 ≤ (22033018260149/50000000000000 : ℝ)^3219 := by
    have hnat : (1074052369 : ℕ)^4243*50000000000000^3219 ≤ 22033018260149^3219*2000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074052369 2000000000 22033018260149 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253274403/10000000000 : ℝ)^4243 ≤ (2805220349857/20000000000000 : ℝ)^3219 := by
    have hnat : (2253274403 : ℕ)^4243*20000000000000^3219 ≤ 2805220349857^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253274403 10000000000 2805220349857 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169519829/10000000000 : ℝ)^4243 ≤ (41907861728783/100000000000000 : ℝ)^3219 := by
    have hnat : (5169519829 : ℕ)^4243*100000000000000^3219 ≤ 41907861728783^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169519829 10000000000 41907861728783 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074052369/2000000000 : ℝ), (-2253274403/10000000000 : ℝ), (5169519829/10000000000 : ℝ)] ![(22033018260149/50000000000000 : ℝ), (2805220349857/20000000000000 : ℝ), (41907861728783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074052369/2000000000 : ℝ)|^4243 ≤ (22033018260149/50000000000000 : ℝ)^3219
        have hw : |(1074052369/2000000000 : ℝ)|=(1074052369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2253274403/10000000000 : ℝ)|^4243 ≤ (2805220349857/20000000000000 : ℝ)^3219
        have hw : |(-2253274403/10000000000 : ℝ)|=(2253274403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169519829/10000000000 : ℝ)|^4243 ≤ (41907861728783/100000000000000 : ℝ)^3219
        have hw : |(5169519829/10000000000 : ℝ)|=(5169519829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s2_2 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268513111/500000000 : ℝ)*x 0 + (5169519271/10000000000 : ℝ)*x 1 + (-1126637317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268513111/500000000 : ℝ)^4243 ≤ (44066040576241/100000000000000 : ℝ)^3219 := by
    have hnat : (268513111 : ℕ)^4243*100000000000000^3219 ≤ 44066040576241^3219*500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268513111 500000000 44066040576241 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5169519271/10000000000 : ℝ)^4243 ≤ (261924098539/625000000000 : ℝ)^3219 := by
    have hnat : (5169519271 : ℕ)^4243*625000000000^3219 ≤ 261924098539^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169519271 10000000000 261924098539 625000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126637317/5000000000 : ℝ)^4243 ≤ (876631477789/6250000000000 : ℝ)^3219 := by
    have hnat : (1126637317 : ℕ)^4243*6250000000000^3219 ≤ 876631477789^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126637317 5000000000 876631477789 6250000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268513111/500000000 : ℝ), (5169519271/10000000000 : ℝ), (-1126637317/5000000000 : ℝ)] ![(44066040576241/100000000000000 : ℝ), (261924098539/625000000000 : ℝ), (876631477789/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268513111/500000000 : ℝ)|^4243 ≤ (44066040576241/100000000000000 : ℝ)^3219
        have hw : |(268513111/500000000 : ℝ)|=(268513111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5169519271/10000000000 : ℝ)|^4243 ≤ (261924098539/625000000000 : ℝ)^3219
        have hw : |(5169519271/10000000000 : ℝ)|=(5169519271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126637317/5000000000 : ℝ)|^4243 ≤ (876631477789/6250000000000 : ℝ)^3219
        have hw : |(-1126637317/5000000000 : ℝ)|=(1126637317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s2_3 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (173373679/400000000 : ℝ)*x 0 + (501417111/1250000000 : ℝ)*x 1 + (4682181127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173373679/400000000 : ℝ)^4243 ≤ (16610946054343/50000000000000 : ℝ)^3219 := by
    have hnat : (173373679 : ℕ)^4243*50000000000000^3219 ≤ 16610946054343^3219*400000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173373679 400000000 16610946054343 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501417111/1250000000 : ℝ)^4243 ≤ (29997907586907/100000000000000 : ℝ)^3219 := by
    have hnat : (501417111 : ℕ)^4243*100000000000000^3219 ≤ 29997907586907^3219*1250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501417111 1250000000 29997907586907 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4682181127/10000000000 : ℝ)^4243 ≤ (7356040057753/20000000000000 : ℝ)^3219 := by
    have hnat : (4682181127 : ℕ)^4243*20000000000000^3219 ≤ 7356040057753^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4682181127 10000000000 7356040057753 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173373679/400000000 : ℝ), (501417111/1250000000 : ℝ), (4682181127/10000000000 : ℝ)] ![(16610946054343/50000000000000 : ℝ), (29997907586907/100000000000000 : ℝ), (7356040057753/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173373679/400000000 : ℝ)|^4243 ≤ (16610946054343/50000000000000 : ℝ)^3219
        have hw : |(173373679/400000000 : ℝ)|=(173373679/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501417111/1250000000 : ℝ)|^4243 ≤ (29997907586907/100000000000000 : ℝ)^3219
        have hw : |(501417111/1250000000 : ℝ)|=(501417111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4682181127/10000000000 : ℝ)|^4243 ≤ (7356040057753/20000000000000 : ℝ)^3219
        have hw : |(4682181127/10000000000 : ℝ)|=(4682181127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s2_4 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083531841/10000000000 : ℝ)*x 0 + (1292929183/2500000000 : ℝ)*x 1 + (5494831061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083531841/10000000000 : ℝ)^4243 ≤ (12650358334257/100000000000000 : ℝ)^3219 := by
    have hnat : (2083531841 : ℕ)^4243*100000000000000^3219 ≤ 12650358334257^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083531841 10000000000 12650358334257 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292929183/2500000000 : ℝ)^4243 ≤ (4193133845773/10000000000000 : ℝ)^3219 := by
    have hnat : (1292929183 : ℕ)^4243*10000000000000^3219 ≤ 4193133845773^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292929183 2500000000 4193133845773 10000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494831061/10000000000 : ℝ)^4243 ≤ (9083660640277/20000000000000 : ℝ)^3219 := by
    have hnat : (5494831061 : ℕ)^4243*20000000000000^3219 ≤ 9083660640277^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494831061 10000000000 9083660640277 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083531841/10000000000 : ℝ), (1292929183/2500000000 : ℝ), (5494831061/10000000000 : ℝ)] ![(12650358334257/100000000000000 : ℝ), (4193133845773/10000000000000 : ℝ), (9083660640277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083531841/10000000000 : ℝ)|^4243 ≤ (12650358334257/100000000000000 : ℝ)^3219
        have hw : |(-2083531841/10000000000 : ℝ)|=(2083531841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292929183/2500000000 : ℝ)|^4243 ≤ (4193133845773/10000000000000 : ℝ)^3219
        have hw : |(1292929183/2500000000 : ℝ)|=(1292929183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494831061/10000000000 : ℝ)|^4243 ≤ (9083660640277/20000000000000 : ℝ)^3219
        have hw : |(5494831061/10000000000 : ℝ)|=(5494831061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s2_5 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643202699/5000000000 : ℝ)*x 0 + (-1927962497/10000000000 : ℝ)*x 1 + (2747415607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643202699/5000000000 : ℝ)^4243 ≤ (43161318581971/100000000000000 : ℝ)^3219 := by
    have hnat : (2643202699 : ℕ)^4243*100000000000000^3219 ≤ 43161318581971^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643202699 5000000000 43161318581971 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927962497/10000000000 : ℝ)^4243 ≤ (11420376538063/100000000000000 : ℝ)^3219 := by
    have hnat : (1927962497 : ℕ)^4243*100000000000000^3219 ≤ 11420376538063^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927962497 10000000000 11420376538063 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747415607/5000000000 : ℝ)^4243 ≤ (1816732194733/4000000000000 : ℝ)^3219 := by
    have hnat : (2747415607 : ℕ)^4243*4000000000000^3219 ≤ 1816732194733^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747415607 5000000000 1816732194733 4000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643202699/5000000000 : ℝ), (-1927962497/10000000000 : ℝ), (2747415607/5000000000 : ℝ)] ![(43161318581971/100000000000000 : ℝ), (11420376538063/100000000000000 : ℝ), (1816732194733/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643202699/5000000000 : ℝ)|^4243 ≤ (43161318581971/100000000000000 : ℝ)^3219
        have hw : |(2643202699/5000000000 : ℝ)|=(2643202699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1927962497/10000000000 : ℝ)|^4243 ≤ (11420376538063/100000000000000 : ℝ)^3219
        have hw : |(-1927962497/10000000000 : ℝ)|=(1927962497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747415607/5000000000 : ℝ)|^4243 ≤ (1816732194733/4000000000000 : ℝ)^3219
        have hw : |(2747415607/5000000000 : ℝ)|=(2747415607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s2_6 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286405579/10000000000 : ℝ)*x 0 + (549483107/1000000000 : ℝ)*x 1 + (-120497653/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286405579/10000000000 : ℝ)^4243 ≤ (21580660264931/50000000000000 : ℝ)^3219 := by
    have hnat : (5286405579 : ℕ)^4243*50000000000000^3219 ≤ 21580660264931^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286405579 10000000000 21580660264931 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549483107/1000000000 : ℝ)^4243 ≤ (567728791243/1250000000000 : ℝ)^3219 := by
    have hnat : (549483107 : ℕ)^4243*1250000000000^3219 ≤ 567728791243^3219*1000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549483107 1000000000 567728791243 1250000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120497653/625000000 : ℝ)^4243 ≤ (2855094038869/25000000000000 : ℝ)^3219 := by
    have hnat : (120497653 : ℕ)^4243*25000000000000^3219 ≤ 2855094038869^3219*625000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120497653 625000000 2855094038869 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286405579/10000000000 : ℝ), (549483107/1000000000 : ℝ), (-120497653/625000000 : ℝ)] ![(21580660264931/50000000000000 : ℝ), (567728791243/1250000000000 : ℝ), (2855094038869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286405579/10000000000 : ℝ)|^4243 ≤ (21580660264931/50000000000000 : ℝ)^3219
        have hw : |(5286405579/10000000000 : ℝ)|=(5286405579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549483107/1000000000 : ℝ)|^4243 ≤ (567728791243/1250000000000 : ℝ)^3219
        have hw : |(549483107/1000000000 : ℝ)|=(549483107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120497653/625000000 : ℝ)|^4243 ≤ (2855094038869/25000000000000 : ℝ)^3219
        have hw : |(-120497653/625000000 : ℝ)|=(120497653/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s2_7 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (108362939/250000000 : ℝ)*x 0 + (1169419753/2500000000 : ℝ)*x 1 + (4015884503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108362939/250000000 : ℝ)^4243 ≤ (33223666067183/100000000000000 : ℝ)^3219 := by
    have hnat : (108362939 : ℕ)^4243*100000000000000^3219 ≤ 33223666067183^3219*250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108362939 250000000 33223666067183 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1169419753/2500000000 : ℝ)^4243 ≤ (36733591471867/100000000000000 : ℝ)^3219 := by
    have hnat : (1169419753 : ℕ)^4243*100000000000000^3219 ≤ 36733591471867^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169419753 2500000000 36733591471867 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4015884503/10000000000 : ℝ)^4243 ≤ (15021371225399/50000000000000 : ℝ)^3219 := by
    have hnat : (4015884503 : ℕ)^4243*50000000000000^3219 ≤ 15021371225399^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015884503 10000000000 15021371225399 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108362939/250000000 : ℝ), (1169419753/2500000000 : ℝ), (4015884503/10000000000 : ℝ)] ![(33223666067183/100000000000000 : ℝ), (36733591471867/100000000000000 : ℝ), (15021371225399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108362939/250000000 : ℝ)|^4243 ≤ (33223666067183/100000000000000 : ℝ)^3219
        have hw : |(108362939/250000000 : ℝ)|=(108362939/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1169419753/2500000000 : ℝ)|^4243 ≤ (36733591471867/100000000000000 : ℝ)^3219
        have hw : |(1169419753/2500000000 : ℝ)|=(1169419753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4015884503/10000000000 : ℝ)|^4243 ≤ (15021371225399/50000000000000 : ℝ)^3219
        have hw : |(4015884503/10000000000 : ℝ)|=(4015884503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1283_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19923/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3159/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4719/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16359/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19923/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3159/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19923/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3159/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19923/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3159/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19923/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3159/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19923/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3159/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19923/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3159/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3159/50000 : ℝ) ^ (2121/512 : ℝ) ≤ (1074749811536541/100000000000000000000 : ℝ) := by
    have hpowers : (3159/50000 : ℝ)^2121 ≤ (1074749811536541/100000000000000000000 : ℝ)^512 := by
      have hnat : (3159 : ℕ)^2121*100000000000000000000^512 ≤ 1074749811536541^512*50000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3159 50000 1074749811536541 100000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3159/50000 : ℝ)) (X := (1074749811536541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hpowhi : (19923/100000 : ℝ) ^ (2121/512 : ℝ) ≤ (125176340714852377/100000000000000000000 : ℝ) := by
    have hpowers : (19923/100000 : ℝ)^2121 ≤ (125176340714852377/100000000000000000000 : ℝ)^512 := by
      have hnat : (19923 : ℕ)^2121*100000000000000000000^512 ≤ 125176340714852377^512*100000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19923 100000 125176340714852377 100000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19923/100000 : ℝ)) (X := (125176340714852377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001074749811536541/50000000000000000000 : ℝ) ≤ (2500012971886307/2500000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (50001074749811536541/50000000000000000000 : ℝ)^512 ≤ (2500012971886307/2500000000000000 : ℝ)^2121 := by
      have hnat : (50001074749811536541 : ℕ)^512*2500000000000000^2121 ≤ 2500012971886307^2121*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001074749811536541 50000000000000000000 2500012971886307 2500000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500012971886307/2500000000000000 : ℝ)) (X := (50001074749811536541/50000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50063125545263194459/50000000000000000000 : ℝ) ≤ (312595193344249/312500000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (50063125545263194459/50000000000000000000 : ℝ)^512 ≤ (312595193344249/312500000000000 : ℝ)^2121 := by
      have hnat : (50063125545263194459 : ℕ)^512*312500000000000^2121 ≤ 312595193344249^2121*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50063125545263194459 50000000000000000000 312595193344249 312500000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312595193344249/312500000000000 : ℝ)) (X := (50063125545263194459/50000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50125176340714852377/50000000000000000000 : ℝ) ≤ (2501510121621677/2500000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (50125176340714852377/50000000000000000000 : ℝ)^512 ≤ (2501510121621677/2500000000000000 : ℝ)^2121 := by
      have hnat : (50125176340714852377 : ℕ)^512*2500000000000000^2121 ≤ 2501510121621677^2121*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50125176340714852377 50000000000000000000 2501510121621677 2500000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501510121621677/2500000000000000 : ℝ)) (X := (50125176340714852377/50000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1074749811536541/100000000000000000000 : ℝ) ≤ ((453376233206468521/453500000000000000 : ℝ)+2*(49904991179/22675000000000 : ℝ)*(3159/50000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (453376233206468521/453500000000000000 : ℝ)+2*(49904991179/22675000000000 : ℝ)*(3159/50000 : ℝ)=(2500012971886307/2500000000000000 : ℝ) by norm_num, show 1+2*(1074749811536541/100000000000000000000 : ℝ)=(50001074749811536541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(125176340714852377/100000000000000000000 : ℝ)+(1074749811536541/100000000000000000000 : ℝ) ≤ ((453376233206468521/453500000000000000 : ℝ)+(49904991179/22675000000000 : ℝ)*((19923/100000 : ℝ)+(3159/50000 : ℝ)))^(2121/512 : ℝ) := by
    rw [show (453376233206468521/453500000000000000 : ℝ)+(49904991179/22675000000000 : ℝ)*((19923/100000 : ℝ)+(3159/50000 : ℝ))=(312595193344249/312500000000000 : ℝ) by norm_num, show 1+(125176340714852377/100000000000000000000 : ℝ)+(1074749811536541/100000000000000000000 : ℝ)=(50063125545263194459/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(125176340714852377/100000000000000000000 : ℝ) ≤ ((453376233206468521/453500000000000000 : ℝ)+2*(49904991179/22675000000000 : ℝ)*(19923/100000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (453376233206468521/453500000000000000 : ℝ)+2*(49904991179/22675000000000 : ℝ)*(19923/100000 : ℝ)=(2501510121621677/2500000000000000 : ℝ) by norm_num, show 1+2*(125176340714852377/100000000000000000000 : ℝ)=(50125176340714852377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (453376233206468521/453500000000000000 : ℝ)*(X 1 0+X 2 0)+(49904991179/22675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (3159/50000 : ℝ)) (hi := (19923/100000 : ℝ)) (c := (453376233206468521/453500000000000000 : ℝ)) (alpha := (49904991179/22675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (453376233206468521/453500000000000000 : ℝ)*(X 0 1+X 2 1)+(49904991179/22675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (3159/50000 : ℝ)) (hi := (19923/100000 : ℝ)) (c := (453376233206468521/453500000000000000 : ℝ)) (alpha := (49904991179/22675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (453376233206468521/453500000000000000 : ℝ)*(X 0 2+X 1 2)+(49904991179/22675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (3159/50000 : ℝ)) (hi := (19923/100000 : ℝ)) (c := (453376233206468521/453500000000000000 : ℝ)) (alpha := (49904991179/22675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-65107693/312500000 : ℝ)*X 0 0+(5497049287/10000000000 : ℝ)*X 0 1+(2584759591/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074052369/2000000000 : ℝ)*X 1 0+(-2253274403/10000000000 : ℝ)*X 1 1+(5169519829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268513111/500000000 : ℝ)*X 2 0+(5169519271/10000000000 : ℝ)*X 2 1+(-1126637317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((173373679/400000000 : ℝ)*X 0 0+(501417111/1250000000 : ℝ)*X 0 1+(4682181127/10000000000 : ℝ)*X 0 2+(173373679/400000000 : ℝ)*X 1 0+(501417111/1250000000 : ℝ)*X 1 1+(4682181127/10000000000 : ℝ)*X 1 2+(173373679/400000000 : ℝ)*X 2 0+(501417111/1250000000 : ℝ)*X 2 1+(4682181127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2083531841/10000000000 : ℝ)*X 0 0+(1292929183/2500000000 : ℝ)*X 0 1+(5494831061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643202699/5000000000 : ℝ)*X 1 0+(-1927962497/10000000000 : ℝ)*X 1 1+(2747415607/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5286405579/10000000000 : ℝ)*X 2 0+(549483107/1000000000 : ℝ)*X 2 1+(-120497653/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108362939/250000000 : ℝ)*X 0 0+(1169419753/2500000000 : ℝ)*X 0 1+(4015884503/10000000000 : ℝ)*X 0 2+(108362939/250000000 : ℝ)*X 1 0+(1169419753/2500000000 : ℝ)*X 1 1+(4015884503/10000000000 : ℝ)*X 1 2+(108362939/250000000 : ℝ)*X 2 0+(1169419753/2500000000 : ℝ)*X 2 1+(4015884503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9283000353541318392597/4535000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1250474479/100000000000000 : ℝ)*(base19) + (141466023/10000000000000 : ℝ)*(base23) + (26322153/100000000000000 : ℝ)*(lower2) + (412707223/100000000000000 : ℝ)*(upper3) + (259195467/100000000000000 : ℝ)*(upper5) + (2271932962287551/100000000000000 : ℝ)*(major0) + (2271932962287551/100000000000000 : ℝ)*(major1) + (2271932962287551/100000000000000 : ℝ)*(major2) + (305316815685741/10000000000000 : ℝ)*(sp0) + (763294715056747/25000000000000 : ℝ)*(sp1) + (3053178696041237/100000000000000 : ℝ)*(sp2) + (745335689924423/50000000000000 : ℝ)*(sp3) + (11953844057/100000000000000 : ℝ)*(sp4) + (7182896257/50000000000000 : ℝ)*(sp7) + (18633571820517/1250000000000 : ℝ)*(f.failure) + (3053180110701467/100000000000000 : ℝ)*(f.sum) + (22290237806261/4535000000000000000000000000 : ℝ)*base65 + (47547704700762071/45350000000000000000000000000000 : ℝ)*base67 + (339090852539087929/45350000000000000000000000000000 : ℝ)*base70 + (364070127591762071/45350000000000000000000000000000 : ℝ)*base71 + (3349988355337/566875000000000000000000000 : ℝ)*base73 + (580318928698337929/45350000000000000000000000000000 : ℝ)*base76 + (49908307343762071/45350000000000000000000000000000 : ℝ)*base77 + (178084410225787929/45350000000000000000000000000000 : ℝ)*base80 + (2725369368447/2267500000000000000000000000 : ℝ)*base82 + (265343/125000000000000000000 : ℝ)*base89 + (265343/125000000000000000000 : ℝ)*base91 + (265343/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11964692976400731033746199/2267500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (989651317/100000000000000 : ℝ)*(base19) + (321428557/25000000000000 : ℝ)*(base23) + (17135717/10000000000000 : ℝ)*(upper3) + (68165357/100000000000000 : ℝ)*(lower4) + (13469651/25000000000000 : ℝ)*(upper5) + (230296073692591/10000000000000 : ℝ)*(major0) + (230296073692591/10000000000000 : ℝ)*(major1) + (230296073692591/10000000000000 : ℝ)*(major2) + (4946784657/50000000000000 : ℝ)*(sp1) + (2749745303/20000000000000 : ℝ)*(sp2) + (773719316542061/25000000000000 : ℝ)*(sp4) + (1547433191473807/50000000000000 : ℝ)*(sp5) + (3094862231727501/100000000000000 : ℝ)*(sp6) + (755522015898433/50000000000000 : ℝ)*(sp7) + (755522015898433/50000000000000 : ℝ)*(f.failure) + (773719316542061/25000000000000 : ℝ)*(f.sum) + (168013395519/45350000000000000000000000 : ℝ)*base66 + (10534410356792089/4535000000000000000000000000000 : ℝ)*base68 + (5243695607662089/4535000000000000000000000000000 : ℝ)*base70 + (45460153518962089/4535000000000000000000000000000 : ℝ)*base72 + (181993923167/226750000000000000000000000 : ℝ)*base73 + (66284450122292089/4535000000000000000000000000000 : ℝ)*base76 + (41256420199157089/4535000000000000000000000000000 : ℝ)*base78 + (2587131359237089/4535000000000000000000000000000 : ℝ)*base80 + (70783338729/113375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (81856707/5000000000000000000000 : ℝ)*base89 + (81856707/5000000000000000000000 : ℝ)*base91 + (81856707/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1283_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19923/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3159/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1283_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1283_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1283_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1283_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1283_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1283_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
