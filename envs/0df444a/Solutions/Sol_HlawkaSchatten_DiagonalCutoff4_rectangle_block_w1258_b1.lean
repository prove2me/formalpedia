-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1258_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:52:57.724001+00:00
-- url     : https://prove2.me/submissions/72485b64-1653-4ae6-81c6-efecc80145f7

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
theorem support_rectangle_w1258_s3_0 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054950069/5000000000 : ℝ)*x 0 + (216731067/400000000 : ℝ)*x 1 + (5241829523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054950069/5000000000 : ℝ)^8451 ≤ (12827056920377/100000000000000 : ℝ)^6403 := by
    have hnat : (1054950069 : ℕ)^8451*100000000000000^6403 ≤ 12827056920377^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054950069 5000000000 12827056920377 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216731067/400000000 : ℝ)^8451 ≤ (8907721952899/20000000000000 : ℝ)^6403 := by
    have hnat : (216731067 : ℕ)^8451*20000000000000^6403 ≤ 8907721952899^6403*400000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216731067 400000000 8907721952899 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241829523/10000000000 : ℝ)^8451 ≤ (21317166647907/50000000000000 : ℝ)^6403 := by
    have hnat : (5241829523 : ℕ)^8451*50000000000000^6403 ≤ 21317166647907^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241829523 10000000000 21317166647907 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054950069/5000000000 : ℝ), (216731067/400000000 : ℝ), (5241829523/10000000000 : ℝ)] ![(12827056920377/100000000000000 : ℝ), (8907721952899/20000000000000 : ℝ), (21317166647907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054950069/5000000000 : ℝ)|^8451 ≤ (12827056920377/100000000000000 : ℝ)^6403
        have hw : |(-1054950069/5000000000 : ℝ)|=(1054950069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216731067/400000000 : ℝ)|^8451 ≤ (8907721952899/20000000000000 : ℝ)^6403
        have hw : |(216731067/400000000 : ℝ)|=(216731067/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241829523/10000000000 : ℝ)|^8451 ≤ (21317166647907/50000000000000 : ℝ)^6403
        have hw : |(5241829523/10000000000 : ℝ)|=(5241829523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s3_1 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675570267/5000000000 : ℝ)*x 0 + (-2199886773/10000000000 : ℝ)*x 1 + (2620914811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675570267/5000000000 : ℝ)^8451 ≤ (43811679793491/100000000000000 : ℝ)^6403 := by
    have hnat : (2675570267 : ℕ)^8451*100000000000000^6403 ≤ 43811679793491^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675570267 5000000000 43811679793491 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199886773/10000000000 : ℝ)^8451 ≤ (13553985832267/100000000000000 : ℝ)^6403 := by
    have hnat : (2199886773 : ℕ)^8451*100000000000000^6403 ≤ 13553985832267^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199886773 10000000000 13553985832267 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620914811/5000000000 : ℝ)^8451 ≤ (42634334358577/100000000000000 : ℝ)^6403 := by
    have hnat : (2620914811 : ℕ)^8451*100000000000000^6403 ≤ 42634334358577^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620914811 5000000000 42634334358577 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675570267/5000000000 : ℝ), (-2199886773/10000000000 : ℝ), (2620914811/5000000000 : ℝ)] ![(43811679793491/100000000000000 : ℝ), (13553985832267/100000000000000 : ℝ), (42634334358577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675570267/5000000000 : ℝ)|^8451 ≤ (43811679793491/100000000000000 : ℝ)^6403
        have hw : |(2675570267/5000000000 : ℝ)|=(2675570267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2199886773/10000000000 : ℝ)|^8451 ≤ (13553985832267/100000000000000 : ℝ)^6403
        have hw : |(-2199886773/10000000000 : ℝ)|=(2199886773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620914811/5000000000 : ℝ)|^8451 ≤ (42634334358577/100000000000000 : ℝ)^6403
        have hw : |(2620914811/5000000000 : ℝ)|=(2620914811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s3_2 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668892563/1250000000 : ℝ)*x 0 + (5241830097/10000000000 : ℝ)*x 1 + (-1099943093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668892563/1250000000 : ℝ)^8451 ≤ (10952919867327/25000000000000 : ℝ)^6403 := by
    have hnat : (668892563 : ℕ)^8451*25000000000000^6403 ≤ 10952919867327^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668892563 1250000000 10952919867327 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241830097/10000000000 : ℝ)^8451 ≤ (10658584864423/25000000000000 : ℝ)^6403 := by
    have hnat : (5241830097 : ℕ)^8451*25000000000000^6403 ≤ 10658584864423^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241830097 10000000000 10658584864423 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099943093/5000000000 : ℝ)^8451 ≤ (271079621177/2000000000000 : ℝ)^6403 := by
    have hnat : (1099943093 : ℕ)^8451*2000000000000^6403 ≤ 271079621177^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099943093 5000000000 271079621177 2000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668892563/1250000000 : ℝ), (5241830097/10000000000 : ℝ), (-1099943093/5000000000 : ℝ)] ![(10952919867327/25000000000000 : ℝ), (10658584864423/25000000000000 : ℝ), (271079621177/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668892563/1250000000 : ℝ)|^8451 ≤ (10952919867327/25000000000000 : ℝ)^6403
        have hw : |(668892563/1250000000 : ℝ)|=(668892563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241830097/10000000000 : ℝ)|^8451 ≤ (10658584864423/25000000000000 : ℝ)^6403
        have hw : |(5241830097/10000000000 : ℝ)|=(5241830097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1099943093/5000000000 : ℝ)|^8451 ≤ (271079621177/2000000000000 : ℝ)^6403
        have hw : |(-1099943093/5000000000 : ℝ)|=(1099943093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s3_3 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173480253/5000000000 : ℝ)*x 0 + (4171027867/10000000000 : ℝ)*x 1 + (1132516939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173480253/5000000000 : ℝ)^8451 ≤ (33301160121291/100000000000000 : ℝ)^6403 := by
    have hnat : (2173480253 : ℕ)^8451*100000000000000^6403 ≤ 33301160121291^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173480253 5000000000 33301160121291 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171027867/10000000000 : ℝ)^8451 ≤ (1970869346561/6250000000000 : ℝ)^6403 := by
    have hnat : (4171027867 : ℕ)^8451*6250000000000^6403 ≤ 1970869346561^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171027867 10000000000 1970869346561 6250000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132516939/2500000000 : ℝ)^8451 ≤ (17582465160497/50000000000000 : ℝ)^6403 := by
    have hnat : (1132516939 : ℕ)^8451*50000000000000^6403 ≤ 17582465160497^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132516939 2500000000 17582465160497 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173480253/5000000000 : ℝ), (4171027867/10000000000 : ℝ), (1132516939/2500000000 : ℝ)] ![(33301160121291/100000000000000 : ℝ), (1970869346561/6250000000000 : ℝ), (17582465160497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173480253/5000000000 : ℝ)|^8451 ≤ (33301160121291/100000000000000 : ℝ)^6403
        have hw : |(2173480253/5000000000 : ℝ)|=(2173480253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171027867/10000000000 : ℝ)|^8451 ≤ (1970869346561/6250000000000 : ℝ)^6403
        have hw : |(4171027867/10000000000 : ℝ)|=(4171027867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132516939/2500000000 : ℝ)|^8451 ≤ (17582465160497/50000000000000 : ℝ)^6403
        have hw : |(1132516939/2500000000 : ℝ)|=(1132516939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s3_4 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109914217/10000000000 : ℝ)*x 0 + (20478377/39062500 : ℝ)*x 1 + (5417637939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109914217/10000000000 : ℝ)^8451 ≤ (6413584945041/50000000000000 : ℝ)^6403 := by
    have hnat : (2109914217 : ℕ)^8451*50000000000000^6403 ≤ 6413584945041^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109914217 10000000000 6413584945041 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20478377/39062500 : ℝ)^8451 ≤ (42641150021201/100000000000000 : ℝ)^6403 := by
    have hnat : (20478377 : ℕ)^8451*100000000000000^6403 ≤ 42641150021201^6403*39062500^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20478377 39062500 42641150021201 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417637939/10000000000 : ℝ)^8451 ≤ (2226584004141/5000000000000 : ℝ)^6403 := by
    have hnat : (5417637939 : ℕ)^8451*5000000000000^6403 ≤ 2226584004141^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417637939 10000000000 2226584004141 5000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109914217/10000000000 : ℝ), (20478377/39062500 : ℝ), (5417637939/10000000000 : ℝ)] ![(6413584945041/50000000000000 : ℝ), (42641150021201/100000000000000 : ℝ), (2226584004141/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109914217/10000000000 : ℝ)|^8451 ≤ (6413584945041/50000000000000 : ℝ)^6403
        have hw : |(-2109914217/10000000000 : ℝ)|=(2109914217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20478377/39062500 : ℝ)|^8451 ≤ (42641150021201/100000000000000 : ℝ)^6403
        have hw : |(20478377/39062500 : ℝ)|=(20478377/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417637939/10000000000 : ℝ)|^8451 ≤ (2226584004141/5000000000000 : ℝ)^6403
        have hw : |(5417637939/10000000000 : ℝ)|=(5417637939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s3_5 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5306077243/10000000000 : ℝ)*x 0 + (-1012038913/5000000000 : ℝ)*x 1 + (5417637777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5306077243/10000000000 : ℝ)^8451 ≤ (43325379375621/100000000000000 : ℝ)^6403 := by
    have hnat : (5306077243 : ℕ)^8451*100000000000000^6403 ≤ 43325379375621^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306077243 10000000000 43325379375621 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012038913/5000000000 : ℝ)^8451 ≤ (12142942278639/100000000000000 : ℝ)^6403 := by
    have hnat : (1012038913 : ℕ)^8451*100000000000000^6403 ≤ 12142942278639^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012038913 5000000000 12142942278639 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417637777/10000000000 : ℝ)^8451 ≤ (22265839162653/50000000000000 : ℝ)^6403 := by
    have hnat : (5417637777 : ℕ)^8451*50000000000000^6403 ≤ 22265839162653^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417637777 10000000000 22265839162653 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5306077243/10000000000 : ℝ), (-1012038913/5000000000 : ℝ), (5417637777/10000000000 : ℝ)] ![(43325379375621/100000000000000 : ℝ), (12142942278639/100000000000000 : ℝ), (22265839162653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5306077243/10000000000 : ℝ)|^8451 ≤ (43325379375621/100000000000000 : ℝ)^6403
        have hw : |(5306077243/10000000000 : ℝ)|=(5306077243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1012038913/5000000000 : ℝ)|^8451 ≤ (12142942278639/100000000000000 : ℝ)^6403
        have hw : |(-1012038913/5000000000 : ℝ)|=(1012038913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417637777/10000000000 : ℝ)|^8451 ≤ (22265839162653/50000000000000 : ℝ)^6403
        have hw : |(5417637777/10000000000 : ℝ)|=(5417637777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s3_6 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5306076593/10000000000 : ℝ)*x 0 + (5417638229/10000000000 : ℝ)*x 1 + (-506019523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5306076593/10000000000 : ℝ)^8451 ≤ (43325372370643/100000000000000 : ℝ)^6403 := by
    have hnat : (5306076593 : ℕ)^8451*100000000000000^6403 ≤ 43325372370643^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306076593 10000000000 43325372370643 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417638229/10000000000 : ℝ)^8451 ≤ (22265841614493/50000000000000 : ℝ)^6403 := by
    have hnat : (5417638229 : ℕ)^8451*50000000000000^6403 ≤ 22265841614493^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417638229 10000000000 22265841614493 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506019523/2500000000 : ℝ)^8451 ≤ (1517868048107/12500000000000 : ℝ)^6403 := by
    have hnat : (506019523 : ℕ)^8451*12500000000000^6403 ≤ 1517868048107^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506019523 2500000000 1517868048107 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5306076593/10000000000 : ℝ), (5417638229/10000000000 : ℝ), (-506019523/2500000000 : ℝ)] ![(43325372370643/100000000000000 : ℝ), (22265841614493/50000000000000 : ℝ), (1517868048107/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5306076593/10000000000 : ℝ)|^8451 ≤ (43325372370643/100000000000000 : ℝ)^6403
        have hw : |(5306076593/10000000000 : ℝ)|=(5306076593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417638229/10000000000 : ℝ)|^8451 ≤ (22265841614493/50000000000000 : ℝ)^6403
        have hw : |(5417638229/10000000000 : ℝ)|=(5417638229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506019523/2500000000 : ℝ)|^8451 ≤ (1517868048107/12500000000000 : ℝ)^6403
        have hw : |(-506019523/2500000000 : ℝ)|=(506019523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s3_7 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173494307/5000000000 : ℝ)*x 0 + (905754977/2000000000 : ℝ)*x 1 + (1043081683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173494307/5000000000 : ℝ)^8451 ≤ (16650722162147/50000000000000 : ℝ)^6403 := by
    have hnat : (2173494307 : ℕ)^8451*50000000000000^6403 ≤ 16650722162147^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173494307 5000000000 16650722162147 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905754977/2000000000 : ℝ)^8451 ≤ (17575842461179/50000000000000 : ℝ)^6403 := by
    have hnat : (905754977 : ℕ)^8451*50000000000000^6403 ≤ 17575842461179^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905754977 2000000000 17575842461179 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043081683/2500000000 : ℝ)^8451 ≤ (15773435368821/50000000000000 : ℝ)^6403 := by
    have hnat : (1043081683 : ℕ)^8451*50000000000000^6403 ≤ 15773435368821^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043081683 2500000000 15773435368821 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173494307/5000000000 : ℝ), (905754977/2000000000 : ℝ), (1043081683/2500000000 : ℝ)] ![(16650722162147/50000000000000 : ℝ), (17575842461179/50000000000000 : ℝ), (15773435368821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173494307/5000000000 : ℝ)|^8451 ≤ (16650722162147/50000000000000 : ℝ)^6403
        have hw : |(2173494307/5000000000 : ℝ)|=(2173494307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(905754977/2000000000 : ℝ)|^8451 ≤ (17575842461179/50000000000000 : ℝ)^6403
        have hw : |(905754977/2000000000 : ℝ)|=(905754977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043081683/2500000000 : ℝ)|^8451 ≤ (15773435368821/50000000000000 : ℝ)^6403
        have hw : |(1043081683/2500000000 : ℝ)|=(1043081683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1258_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8091/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2391/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1369/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14687/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8091/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2391/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8091/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2391/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8091/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2391/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8091/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2391/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8091/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2391/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8091/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2391/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (2391/25000 : ℝ) ^ (4225/1024 : ℝ) ≤ (3112524301017853/50000000000000000000 : ℝ) := by
    have hpowers : (2391/25000 : ℝ)^4225 ≤ (3112524301017853/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2391 : ℕ)^4225*50000000000000000000^1024 ≤ 3112524301017853^1024*25000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2391 25000 3112524301017853 50000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2391/25000 : ℝ)) (X := (3112524301017853/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8091/50000 : ℝ) ^ (4225/1024 : ℝ) ≤ (54511154793921831/100000000000000000000 : ℝ) := by
    have hpowers : (8091/50000 : ℝ)^4225 ≤ (54511154793921831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8091 : ℕ)^4225*100000000000000000000^1024 ≤ 54511154793921831^1024*50000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8091 50000 54511154793921831 100000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8091/50000 : ℝ)) (X := (54511154793921831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003112524301017853/25000000000000000000 : ℝ) ≤ (10000301734871103/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (25003112524301017853/25000000000000000000 : ℝ)^1024 ≤ (10000301734871103/10000000000000000 : ℝ)^4225 := by
      have hnat : (25003112524301017853 : ℕ)^1024*10000000000000000^4225 ≤ 10000301734871103^4225*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003112524301017853 25000000000000000000 10000301734871103 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000301734871103/10000000000000000 : ℝ)) (X := (25003112524301017853/25000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060736203395957537/100000000000000000000 : ℝ) ≤ (1250183963218567/1250000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (100060736203395957537/100000000000000000000 : ℝ)^1024 ≤ (1250183963218567/1250000000000000 : ℝ)^4225 := by
      have hnat : (100060736203395957537 : ℕ)^1024*1250000000000000^4225 ≤ 1250183963218567^4225*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060736203395957537 100000000000000000000 1250183963218567 1250000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250183963218567/1250000000000000 : ℝ)) (X := (100060736203395957537/100000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50054511154793921831/50000000000000000000 : ℝ) ≤ (10002641676625969/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (50054511154793921831/50000000000000000000 : ℝ)^1024 ≤ (10002641676625969/10000000000000000 : ℝ)^4225 := by
      have hnat : (50054511154793921831 : ℕ)^1024*10000000000000000^4225 ≤ 10002641676625969^4225*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054511154793921831 50000000000000000000 10002641676625969 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002641676625969/10000000000000000 : ℝ)) (X := (50054511154793921831/50000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3112524301017853/50000000000000000000 : ℝ) ≤ ((2205320589281114041/2206000000000000000 : ℝ)+2*(1169970877433/661800000000000 : ℝ)*(2391/25000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (2205320589281114041/2206000000000000000 : ℝ)+2*(1169970877433/661800000000000 : ℝ)*(2391/25000 : ℝ)=(10000301734871103/10000000000000000 : ℝ) by norm_num, show 1+2*(3112524301017853/50000000000000000000 : ℝ)=(25003112524301017853/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54511154793921831/100000000000000000000 : ℝ)+(3112524301017853/50000000000000000000 : ℝ) ≤ ((2205320589281114041/2206000000000000000 : ℝ)+(1169970877433/661800000000000 : ℝ)*((8091/50000 : ℝ)+(2391/25000 : ℝ)))^(4225/1024 : ℝ) := by
    rw [show (2205320589281114041/2206000000000000000 : ℝ)+(1169970877433/661800000000000 : ℝ)*((8091/50000 : ℝ)+(2391/25000 : ℝ))=(1250183963218567/1250000000000000 : ℝ) by norm_num, show 1+(54511154793921831/100000000000000000000 : ℝ)+(3112524301017853/50000000000000000000 : ℝ)=(100060736203395957537/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54511154793921831/100000000000000000000 : ℝ) ≤ ((2205320589281114041/2206000000000000000 : ℝ)+2*(1169970877433/661800000000000 : ℝ)*(8091/50000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (2205320589281114041/2206000000000000000 : ℝ)+2*(1169970877433/661800000000000 : ℝ)*(8091/50000 : ℝ)=(10002641676625969/10000000000000000 : ℝ) by norm_num, show 1+2*(54511154793921831/100000000000000000000 : ℝ)=(50054511154793921831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2205320589281114041/2206000000000000000 : ℝ)*(X 1 0+X 2 0)+(1169970877433/661800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (2391/25000 : ℝ)) (hi := (8091/50000 : ℝ)) (c := (2205320589281114041/2206000000000000000 : ℝ)) (alpha := (1169970877433/661800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2205320589281114041/2206000000000000000 : ℝ)*(X 0 1+X 2 1)+(1169970877433/661800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (2391/25000 : ℝ)) (hi := (8091/50000 : ℝ)) (c := (2205320589281114041/2206000000000000000 : ℝ)) (alpha := (1169970877433/661800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2205320589281114041/2206000000000000000 : ℝ)*(X 0 2+X 1 2)+(1169970877433/661800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (2391/25000 : ℝ)) (hi := (8091/50000 : ℝ)) (c := (2205320589281114041/2206000000000000000 : ℝ)) (alpha := (1169970877433/661800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1054950069/5000000000 : ℝ)*X 0 0+(216731067/400000000 : ℝ)*X 0 1+(5241829523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675570267/5000000000 : ℝ)*X 1 0+(-2199886773/10000000000 : ℝ)*X 1 1+(2620914811/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668892563/1250000000 : ℝ)*X 2 0+(5241830097/10000000000 : ℝ)*X 2 1+(-1099943093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173480253/5000000000 : ℝ)*X 0 0+(4171027867/10000000000 : ℝ)*X 0 1+(1132516939/2500000000 : ℝ)*X 0 2+(2173480253/5000000000 : ℝ)*X 1 0+(4171027867/10000000000 : ℝ)*X 1 1+(1132516939/2500000000 : ℝ)*X 1 2+(2173480253/5000000000 : ℝ)*X 2 0+(4171027867/10000000000 : ℝ)*X 2 1+(1132516939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2109914217/10000000000 : ℝ)*X 0 0+(20478377/39062500 : ℝ)*X 0 1+(5417637939/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5306077243/10000000000 : ℝ)*X 1 0+(-1012038913/5000000000 : ℝ)*X 1 1+(5417637777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5306076593/10000000000 : ℝ)*X 2 0+(5417638229/10000000000 : ℝ)*X 2 1+(-506019523/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173494307/5000000000 : ℝ)*X 0 0+(905754977/2000000000 : ℝ)*X 0 1+(1043081683/2500000000 : ℝ)*X 0 2+(2173494307/5000000000 : ℝ)*X 1 0+(905754977/2000000000 : ℝ)*X 1 1+(1043081683/2500000000 : ℝ)*X 1 2+(2173494307/5000000000 : ℝ)*X 2 0+(905754977/2000000000 : ℝ)*X 2 1+(1043081683/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (88053470720500191429664467/27575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12195867/50000000000000 : ℝ)*(base8) + (7552169/6250000000000 : ℝ)*(lower2) + (5484889/5000000000000 : ℝ)*(lower3) + (36412663/50000000000000 : ℝ)*(lower4) + (2113169251162329/50000000000000 : ℝ)*(major0) + (2113169251162329/50000000000000 : ℝ)*(major1) + (2113169251162329/50000000000000 : ℝ)*(major2) + (5667438403141929/100000000000000 : ℝ)*(sp0) + (17710776830651/312500000000 : ℝ)*(sp1) + (5667463012578293/100000000000000 : ℝ)*(sp2) + (2785210282766621/100000000000000 : ℝ)*(sp3) + (2458504463/10000000000000 : ℝ)*(sp4) + (3606692493/25000000000000 : ℝ)*(sp5) + (3602863203/100000000000000 : ℝ)*(sp7) + (21759483481483/781250000000 : ℝ)*(f.failure) + (5667463012578293/100000000000000 : ℝ)*(f.sum) + (22077008766479/5515000000000000000000000000 : ℝ)*base65 + (2655473605111251489/110300000000000000000000000000000 : ℝ)*base67 + (173251716752348511/110300000000000000000000000000000 : ℝ)*base70 + (759918493132848511/110300000000000000000000000000000 : ℝ)*base72 + (5392334168631/5515000000000000000000000000 : ℝ)*base74 + (404760369876448511/110300000000000000000000000000000 : ℝ)*base76 + (8305771975571648511/110300000000000000000000000000000 : ℝ)*base78 + (266363223684548511/110300000000000000000000000000000 : ℝ)*base80 + (9753390701791/5515000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (323459/78125000000000000000 : ℝ)*base89 + (323459/78125000000000000000 : ℝ)*base91 + (323459/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27893475840661048810239141/3446875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3302878107/100000000000000 : ℝ)*(base19) + (1309811141/50000000000000 : ℝ)*(base23) + (105573959/100000000000000 : ℝ)*(upper3) + (97133949/100000000000000 : ℝ)*(lower4) + (253795549/50000000000000 : ℝ)*(upper5) + (66516268759871/1562500000000 : ℝ)*(major0) + (66516268759871/1562500000000 : ℝ)*(major1) + (66516268759871/1562500000000 : ℝ)*(major2) + (74822726219/100000000000000 : ℝ)*(sp1) + (27578848029/50000000000000 : ℝ)*(sp2) + (2854317377490719/50000000000000 : ℝ)*(sp4) + (713569578672139/12500000000000 : ℝ)*(sp5) + (2854288488831549/50000000000000 : ℝ)*(sp6) + (701361844133881/25000000000000 : ℝ)*(sp7) + (701361844133881/25000000000000 : ℝ)*(f.failure) + (2854317377490719/50000000000000 : ℝ)*(f.sum) + (79926123372763/8272500000000000000000000000 : ℝ)*base65 + (12739877382736367/10340625000000000000000000000000 : ℝ)*base68 + (66934688213630117/10340625000000000000000000000000 : ℝ)*base70 + (40650797268144883/10340625000000000000000000000000 : ℝ)*base71 + (129330440217731/16545000000000000000000000000 : ℝ)*base73 + (22997816821880117/10340625000000000000000000000000 : ℝ)*base76 + (34824133931405117/10340625000000000000000000000000 : ℝ)*base78 + (60923603851926133/10340625000000000000000000000000 : ℝ)*base79 + (4485511289701/4136250000000000000000000000 : ℝ)*base82 + (20912787/2500000000000000000000 : ℝ)*base90 + (20912787/2500000000000000000000 : ℝ)*base92 + (20912787/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1258_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8091/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2391/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1369/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1258_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1258_s4_0 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056046997/5000000000 : ℝ)*x 0 + (2698429861/5000000000 : ℝ)*x 1 + (1315452129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056046997/5000000000 : ℝ)^8451 ≤ (12844663298897/100000000000000 : ℝ)^6403 := by
    have hnat : (1056046997 : ℕ)^8451*100000000000000^6403 ≤ 12844663298897^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056046997 5000000000 12844663298897 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698429861/5000000000 : ℝ)^8451 ≤ (11076599677001/25000000000000 : ℝ)^6403 := by
    have hnat : (2698429861 : ℕ)^8451*25000000000000^6403 ≤ 11076599677001^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698429861 5000000000 11076599677001 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315452129/2500000000 : ℝ)^8451 ≤ (21424468988751/50000000000000 : ℝ)^6403 := by
    have hnat : (1315452129 : ℕ)^8451*50000000000000^6403 ≤ 21424468988751^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315452129 2500000000 21424468988751 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056046997/5000000000 : ℝ), (2698429861/5000000000 : ℝ), (1315452129/2500000000 : ℝ)] ![(12844663298897/100000000000000 : ℝ), (11076599677001/25000000000000 : ℝ), (21424468988751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056046997/5000000000 : ℝ)|^8451 ≤ (12844663298897/100000000000000 : ℝ)^6403
        have hw : |(-1056046997/5000000000 : ℝ)|=(1056046997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698429861/5000000000 : ℝ)|^8451 ≤ (11076599677001/25000000000000 : ℝ)^6403
        have hw : |(2698429861/5000000000 : ℝ)|=(2698429861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315452129/2500000000 : ℝ)|^8451 ≤ (21424468988751/50000000000000 : ℝ)^6403
        have hw : |(1315452129/2500000000 : ℝ)|=(1315452129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s4_1 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (133643349/250000000 : ℝ)*x 0 + (-2180652807/10000000000 : ℝ)*x 1 + (210472341/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133643349/250000000 : ℝ)^8451 ≤ (43753265368803/100000000000000 : ℝ)^6403 := by
    have hnat : (133643349 : ℕ)^8451*100000000000000^6403 ≤ 43753265368803^6403*250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133643349 250000000 43753265368803 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180652807/10000000000 : ℝ)^8451 ≤ (6698898270273/50000000000000 : ℝ)^6403 := by
    have hnat : (2180652807 : ℕ)^8451*50000000000000^6403 ≤ 6698898270273^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180652807 10000000000 6698898270273 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210472341/400000000 : ℝ)^8451 ≤ (8569787614847/20000000000000 : ℝ)^6403 := by
    have hnat : (210472341 : ℕ)^8451*20000000000000^6403 ≤ 8569787614847^6403*400000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210472341 400000000 8569787614847 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133643349/250000000 : ℝ), (-2180652807/10000000000 : ℝ), (210472341/400000000 : ℝ)] ![(43753265368803/100000000000000 : ℝ), (6698898270273/50000000000000 : ℝ), (8569787614847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133643349/250000000 : ℝ)|^8451 ≤ (43753265368803/100000000000000 : ℝ)^6403
        have hw : |(133643349/250000000 : ℝ)|=(133643349/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2180652807/10000000000 : ℝ)|^8451 ≤ (6698898270273/50000000000000 : ℝ)^6403
        have hw : |(-2180652807/10000000000 : ℝ)|=(2180652807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210472341/400000000 : ℝ)|^8451 ≤ (8569787614847/20000000000000 : ℝ)^6403
        have hw : |(210472341/400000000 : ℝ)|=(210472341/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s4_2 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345733989/10000000000 : ℝ)*x 0 + (2630904249/5000000000 : ℝ)*x 1 + (-436130561/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345733989/10000000000 : ℝ)^8451 ≤ (21876632841039/50000000000000 : ℝ)^6403 := by
    have hnat : (5345733989 : ℕ)^8451*50000000000000^6403 ≤ 21876632841039^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345733989 10000000000 21876632841039 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630904249/5000000000 : ℝ)^8451 ≤ (42848937784037/100000000000000 : ℝ)^6403 := by
    have hnat : (2630904249 : ℕ)^8451*100000000000000^6403 ≤ 42848937784037^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630904249 5000000000 42848937784037 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436130561/2000000000 : ℝ)^8451 ≤ (1674724565541/12500000000000 : ℝ)^6403 := by
    have hnat : (436130561 : ℕ)^8451*12500000000000^6403 ≤ 1674724565541^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436130561 2000000000 1674724565541 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345733989/10000000000 : ℝ), (2630904249/5000000000 : ℝ), (-436130561/2000000000 : ℝ)] ![(21876632841039/50000000000000 : ℝ), (42848937784037/100000000000000 : ℝ), (1674724565541/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345733989/10000000000 : ℝ)|^8451 ≤ (21876632841039/50000000000000 : ℝ)^6403
        have hw : |(5345733989/10000000000 : ℝ)|=(5345733989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630904249/5000000000 : ℝ)|^8451 ≤ (42848937784037/100000000000000 : ℝ)^6403
        have hw : |(2630904249/5000000000 : ℝ)|=(2630904249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-436130561/2000000000 : ℝ)|^8451 ≤ (1674724565541/12500000000000 : ℝ)^6403
        have hw : |(-436130561/2000000000 : ℝ)|=(436130561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s4_3 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348277661/10000000000 : ℝ)*x 0 + (210648819/500000000 : ℝ)*x 1 + (560972987/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348277661/10000000000 : ℝ)^8451 ≤ (33314478648333/100000000000000 : ℝ)^6403 := by
    have hnat : (4348277661 : ℕ)^8451*100000000000000^6403 ≤ 33314478648333^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348277661 10000000000 33314478648333 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210648819/500000000 : ℝ)^8451 ≤ (998536211441/3125000000000 : ℝ)^6403 := by
    have hnat : (210648819 : ℕ)^8451*3125000000000^6403 ≤ 998536211441^6403*500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210648819 500000000 998536211441 3125000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560972987/1250000000 : ℝ)^8451 ≤ (34732362574797/100000000000000 : ℝ)^6403 := by
    have hnat : (560972987 : ℕ)^8451*100000000000000^6403 ≤ 34732362574797^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560972987 1250000000 34732362574797 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348277661/10000000000 : ℝ), (210648819/500000000 : ℝ), (560972987/1250000000 : ℝ)] ![(33314478648333/100000000000000 : ℝ), (998536211441/3125000000000 : ℝ), (34732362574797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348277661/10000000000 : ℝ)|^8451 ≤ (33314478648333/100000000000000 : ℝ)^6403
        have hw : |(4348277661/10000000000 : ℝ)|=(4348277661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210648819/500000000 : ℝ)|^8451 ≤ (998536211441/3125000000000 : ℝ)^6403
        have hw : |(210648819/500000000 : ℝ)|=(210648819/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560972987/1250000000 : ℝ)|^8451 ≤ (34732362574797/100000000000000 : ℝ)^6403
        have hw : |(560972987/1250000000 : ℝ)|=(560972987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s4_4 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-211209993/1000000000 : ℝ)*x 0 + (105243623/200000000 : ℝ)*x 1 + (5396485691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211209993/1000000000 : ℝ)^8451 ≤ (6422355472543/50000000000000 : ℝ)^6403 := by
    have hnat : (211209993 : ℕ)^8451*50000000000000^6403 ≤ 6422355472543^6403*1000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211209993 1000000000 6422355472543 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105243623/200000000 : ℝ)^8451 ≤ (21426471555607/50000000000000 : ℝ)^6403 := by
    have hnat : (105243623 : ℕ)^8451*50000000000000^6403 ≤ 21426471555607^6403*200000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105243623 200000000 21426471555607 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396485691/10000000000 : ℝ)^8451 ≤ (2215117296551/5000000000000 : ℝ)^6403 := by
    have hnat : (5396485691 : ℕ)^8451*5000000000000^6403 ≤ 2215117296551^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396485691 10000000000 2215117296551 5000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211209993/1000000000 : ℝ), (105243623/200000000 : ℝ), (5396485691/10000000000 : ℝ)] ![(6422355472543/50000000000000 : ℝ), (21426471555607/50000000000000 : ℝ), (2215117296551/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211209993/1000000000 : ℝ)|^8451 ≤ (6422355472543/50000000000000 : ℝ)^6403
        have hw : |(-211209993/1000000000 : ℝ)|=(211209993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105243623/200000000 : ℝ)|^8451 ≤ (21426471555607/50000000000000 : ℝ)^6403
        have hw : |(105243623/200000000 : ℝ)|=(105243623/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396485691/10000000000 : ℝ)|^8451 ≤ (2215117296551/5000000000000 : ℝ)^6403
        have hw : |(5396485691/10000000000 : ℝ)|=(5396485691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s4_5 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655619879/5000000000 : ℝ)*x 0 + (-5114939/25000000 : ℝ)*x 1 + (5396485667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655619879/5000000000 : ℝ)^8451 ≤ (10845255970303/25000000000000 : ℝ)^6403 := by
    have hnat : (2655619879 : ℕ)^8451*25000000000000^6403 ≤ 10845255970303^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655619879 5000000000 10845255970303 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5114939/25000000 : ℝ)^8451 ≤ (12316630439201/100000000000000 : ℝ)^6403 := by
    have hnat : (5114939 : ℕ)^8451*100000000000000^6403 ≤ 12316630439201^6403*25000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5114939 25000000 12316630439201 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396485667/10000000000 : ℝ)^8451 ≤ (44302345670973/100000000000000 : ℝ)^6403 := by
    have hnat : (5396485667 : ℕ)^8451*100000000000000^6403 ≤ 44302345670973^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396485667 10000000000 44302345670973 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655619879/5000000000 : ℝ), (-5114939/25000000 : ℝ), (5396485667/10000000000 : ℝ)] ![(10845255970303/25000000000000 : ℝ), (12316630439201/100000000000000 : ℝ), (44302345670973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655619879/5000000000 : ℝ)|^8451 ≤ (10845255970303/25000000000000 : ℝ)^6403
        have hw : |(2655619879/5000000000 : ℝ)|=(2655619879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5114939/25000000 : ℝ)|^8451 ≤ (12316630439201/100000000000000 : ℝ)^6403
        have hw : |(-5114939/25000000 : ℝ)|=(5114939/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396485667/10000000000 : ℝ)|^8451 ≤ (44302345670973/100000000000000 : ℝ)^6403
        have hw : |(5396485667/10000000000 : ℝ)|=(5396485667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s4_6 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106224791/200000000 : ℝ)*x 0 + (5396485847/10000000000 : ℝ)*x 1 + (-511493909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106224791/200000000 : ℝ)^8451 ≤ (21690510819461/50000000000000 : ℝ)^6403 := by
    have hnat : (106224791 : ℕ)^8451*50000000000000^6403 ≤ 21690510819461^6403*200000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106224791 200000000 21690510819461 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396485847/10000000000 : ℝ)^8451 ≤ (11075586905331/25000000000000 : ℝ)^6403 := by
    have hnat : (5396485847 : ℕ)^8451*25000000000000^6403 ≤ 11075586905331^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396485847 10000000000 11075586905331 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511493909/2500000000 : ℝ)^8451 ≤ (2463326145047/20000000000000 : ℝ)^6403 := by
    have hnat : (511493909 : ℕ)^8451*20000000000000^6403 ≤ 2463326145047^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511493909 2500000000 2463326145047 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106224791/200000000 : ℝ), (5396485847/10000000000 : ℝ), (-511493909/2500000000 : ℝ)] ![(21690510819461/50000000000000 : ℝ), (11075586905331/25000000000000 : ℝ), (2463326145047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106224791/200000000 : ℝ)|^8451 ≤ (21690510819461/50000000000000 : ℝ)^6403
        have hw : |(106224791/200000000 : ℝ)|=(106224791/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396485847/10000000000 : ℝ)|^8451 ≤ (11075586905331/25000000000000 : ℝ)^6403
        have hw : |(5396485847/10000000000 : ℝ)|=(5396485847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511493909/2500000000 : ℝ)|^8451 ≤ (2463326145047/20000000000000 : ℝ)^6403
        have hw : |(-511493909/2500000000 : ℝ)|=(511493909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s4_7 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348289793/10000000000 : ℝ)*x 0 + (2243512983/5000000000 : ℝ)*x 1 + (2106868743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348289793/10000000000 : ℝ)^8451 ≤ (33314601328101/100000000000000 : ℝ)^6403 := by
    have hnat : (4348289793 : ℕ)^8451*100000000000000^6403 ≤ 33314601328101^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348289793 10000000000 33314601328101 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243512983/5000000000 : ℝ)^8451 ≤ (34724620731849/100000000000000 : ℝ)^6403 := by
    have hnat : (2243512983 : ℕ)^8451*100000000000000^6403 ≤ 34724620731849^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243512983 5000000000 34724620731849 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106868743/5000000000 : ℝ)^8451 ≤ (15980388962807/50000000000000 : ℝ)^6403 := by
    have hnat : (2106868743 : ℕ)^8451*50000000000000^6403 ≤ 15980388962807^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106868743 5000000000 15980388962807 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348289793/10000000000 : ℝ), (2243512983/5000000000 : ℝ), (2106868743/5000000000 : ℝ)] ![(33314601328101/100000000000000 : ℝ), (34724620731849/100000000000000 : ℝ), (15980388962807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348289793/10000000000 : ℝ)|^8451 ≤ (33314601328101/100000000000000 : ℝ)^6403
        have hw : |(4348289793/10000000000 : ℝ)|=(4348289793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243512983/5000000000 : ℝ)|^8451 ≤ (34724620731849/100000000000000 : ℝ)^6403
        have hw : |(2243512983/5000000000 : ℝ)|=(2243512983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2106868743/5000000000 : ℝ)|^8451 ≤ (15980388962807/50000000000000 : ℝ)^6403
        have hw : |(2106868743/5000000000 : ℝ)|=(2106868743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1258_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1369/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5689/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1369/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1369/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1369/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1369/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1369/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1369/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1369/12500 : ℝ) ^ (4225/1024 : ℝ) ≤ (10888609557433007/100000000000000000000 : ℝ) := by
    have hpowers : (1369/12500 : ℝ)^4225 ≤ (10888609557433007/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1369 : ℕ)^4225*100000000000000000000^1024 ≤ 10888609557433007^1024*12500^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1369 12500 10888609557433007 100000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1369/12500 : ℝ)) (X := (10888609557433007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14687/100000 : ℝ) ^ (4225/1024 : ℝ) ≤ (36541424578125733/100000000000000000000 : ℝ) := by
    have hpowers : (14687/100000 : ℝ)^4225 ≤ (36541424578125733/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14687 : ℕ)^4225*100000000000000000000^1024 ≤ 36541424578125733^1024*100000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14687 100000 36541424578125733 100000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14687/100000 : ℝ)) (X := (36541424578125733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010888609557433007/50000000000000000000 : ℝ) ≤ (10000527764093833/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (50010888609557433007/50000000000000000000 : ℝ)^1024 ≤ (10000527764093833/10000000000000000 : ℝ)^4225 := by
      have hnat : (50010888609557433007 : ℕ)^1024*10000000000000000^4225 ≤ 10000527764093833^4225*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010888609557433007 50000000000000000000 10000527764093833 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000527764093833/10000000000000000 : ℝ)) (X := (50010888609557433007/50000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002371501706777937/5000000000000000000 : ℝ) ≤ (10001149340377877/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (5002371501706777937/5000000000000000000 : ℝ)^1024 ≤ (10001149340377877/10000000000000000 : ℝ)^4225 := by
      have hnat : (5002371501706777937 : ℕ)^1024*10000000000000000^4225 ≤ 10001149340377877^4225*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002371501706777937 5000000000000000000 10001149340377877 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001149340377877/10000000000000000 : ℝ)) (X := (5002371501706777937/5000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036541424578125733/50000000000000000000 : ℝ) ≤ (10001770916661921/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (50036541424578125733/50000000000000000000 : ℝ)^1024 ≤ (10001770916661921/10000000000000000 : ℝ)^4225 := by
      have hnat : (50036541424578125733 : ℕ)^1024*10000000000000000^4225 ≤ 10001770916661921^4225*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036541424578125733 50000000000000000000 10001770916661921 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001770916661921/10000000000000000 : ℝ)) (X := (50036541424578125733/50000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10888609557433007/100000000000000000000 : ℝ) ≤ ((37338356191964766479/37350000000000000000 : ℝ)+2*(155394071011/93375000000000 : ℝ)*(1369/12500 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (37338356191964766479/37350000000000000000 : ℝ)+2*(155394071011/93375000000000 : ℝ)*(1369/12500 : ℝ)=(10000527764093833/10000000000000000 : ℝ) by norm_num, show 1+2*(10888609557433007/100000000000000000000 : ℝ)=(50010888609557433007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36541424578125733/100000000000000000000 : ℝ)+(10888609557433007/100000000000000000000 : ℝ) ≤ ((37338356191964766479/37350000000000000000 : ℝ)+(155394071011/93375000000000 : ℝ)*((14687/100000 : ℝ)+(1369/12500 : ℝ)))^(4225/1024 : ℝ) := by
    rw [show (37338356191964766479/37350000000000000000 : ℝ)+(155394071011/93375000000000 : ℝ)*((14687/100000 : ℝ)+(1369/12500 : ℝ))=(10001149340377877/10000000000000000 : ℝ) by norm_num, show 1+(36541424578125733/100000000000000000000 : ℝ)+(10888609557433007/100000000000000000000 : ℝ)=(5002371501706777937/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36541424578125733/100000000000000000000 : ℝ) ≤ ((37338356191964766479/37350000000000000000 : ℝ)+2*(155394071011/93375000000000 : ℝ)*(14687/100000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (37338356191964766479/37350000000000000000 : ℝ)+2*(155394071011/93375000000000 : ℝ)*(14687/100000 : ℝ)=(10001770916661921/10000000000000000 : ℝ) by norm_num, show 1+2*(36541424578125733/100000000000000000000 : ℝ)=(50036541424578125733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37338356191964766479/37350000000000000000 : ℝ)*(X 1 0+X 2 0)+(155394071011/93375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (1369/12500 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (37338356191964766479/37350000000000000000 : ℝ)) (alpha := (155394071011/93375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37338356191964766479/37350000000000000000 : ℝ)*(X 0 1+X 2 1)+(155394071011/93375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (1369/12500 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (37338356191964766479/37350000000000000000 : ℝ)) (alpha := (155394071011/93375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37338356191964766479/37350000000000000000 : ℝ)*(X 0 2+X 1 2)+(155394071011/93375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (1369/12500 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (37338356191964766479/37350000000000000000 : ℝ)) (alpha := (155394071011/93375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056046997/5000000000 : ℝ)*X 0 0+(2698429861/5000000000 : ℝ)*X 0 1+(1315452129/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133643349/250000000 : ℝ)*X 1 0+(-2180652807/10000000000 : ℝ)*X 1 1+(210472341/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345733989/10000000000 : ℝ)*X 2 0+(2630904249/5000000000 : ℝ)*X 2 1+(-436130561/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348277661/10000000000 : ℝ)*X 0 0+(210648819/500000000 : ℝ)*X 0 1+(560972987/1250000000 : ℝ)*X 0 2+(4348277661/10000000000 : ℝ)*X 1 0+(210648819/500000000 : ℝ)*X 1 1+(560972987/1250000000 : ℝ)*X 1 2+(4348277661/10000000000 : ℝ)*X 2 0+(210648819/500000000 : ℝ)*X 2 1+(560972987/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-211209993/1000000000 : ℝ)*X 0 0+(105243623/200000000 : ℝ)*X 0 1+(5396485691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655619879/5000000000 : ℝ)*X 1 0+(-5114939/25000000 : ℝ)*X 1 1+(5396485667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106224791/200000000 : ℝ)*X 2 0+(5396485847/10000000000 : ℝ)*X 2 1+(-511493909/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348289793/10000000000 : ℝ)*X 0 0+(2243512983/5000000000 : ℝ)*X 0 1+(2106868743/5000000000 : ℝ)*X 0 2+(4348289793/10000000000 : ℝ)*X 1 0+(2243512983/5000000000 : ℝ)*X 1 1+(2106868743/5000000000 : ℝ)*X 1 2+(4348289793/10000000000 : ℝ)*X 2 0+(2243512983/5000000000 : ℝ)*X 2 1+(2106868743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (282904478078498925316246479/103750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (338942077/50000000000000 : ℝ)*(base19) + (328241547/50000000000000 : ℝ)*(base23) + (6588507/6250000000000 : ℝ)*(upper3) + (32913867/100000000000000 : ℝ)*(upper4) + (72027791/100000000000000 : ℝ)*(upper5) + (2760889752539997/50000000000000 : ℝ)*(major0) + (2760889752539997/50000000000000 : ℝ)*(major1) + (2760889752539997/50000000000000 : ℝ)*(major2) + (7404615482120487/100000000000000 : ℝ)*(sp0) + (7404631320958511/100000000000000 : ℝ)*(sp1) + (7404631342359571/100000000000000 : ℝ)*(sp2) + (1819459108847097/50000000000000 : ℝ)*(sp3) + (8258361089/50000000000000 : ℝ)*(sp4) + (217568253/2500000000000 : ℝ)*(sp7) + (1819463460212157/50000000000000 : ℝ)*(f.failure) + (1480926399768533/20000000000000 : ℝ)*(f.sum) + (423831125543/389062500000000000000000000 : ℝ)*base66 + (28352817177315493/207500000000000000000000000000000 : ℝ)*base68 + (1905609955722684507/207500000000000000000000000000000 : ℝ)*base69 + (1380137262822684507/207500000000000000000000000000000 : ℝ)*base71 + (45399831540263/6225000000000000000000000000 : ℝ)*base74 + (1009815028835184507/207500000000000000000000000000000 : ℝ)*base75 + (1141075957669815493/207500000000000000000000000000000 : ℝ)*base78 + (851537436192684507/207500000000000000000000000000000 : ℝ)*base79 + (4804665747113/6225000000000000000000000000 : ℝ)*base82 + (1765761/5000000000000000000000 : ℝ)*base89 + (1765761/5000000000000000000000 : ℝ)*base91 + (1765761/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2795103760964827927517/518750000000000000000000000 : ℝ) := by norm_num
    linear_combination (802706421/100000000000000 : ℝ)*(base19) + (521144759/100000000000000 : ℝ)*(base23) + (118384587/100000000000000 : ℝ)*(upper3) + (999383/20000000000000 : ℝ)*(lower4) + (10470697/50000000000000 : ℝ)*(upper5) + (5552447392510791/100000000000000 : ℝ)*(major0) + (5552447392510791/100000000000000 : ℝ)*(major1) + (5552447392510791/100000000000000 : ℝ)*(major2) + (17320878893/100000000000000 : ℝ)*(sp1) + (4354155763/25000000000000 : ℝ)*(sp2) + (930719641865239/12500000000000 : ℝ)*(sp4) + (7445739011336597/100000000000000 : ℝ)*(sp5) + (7445739197154101/100000000000000 : ℝ)*(sp6) + (1829568735247297/50000000000000 : ℝ)*(sp7) + (1829568735247297/50000000000000 : ℝ)*(f.failure) + (930719641865239/12500000000000 : ℝ)*(f.sum) + (9083033242091/3112500000000000000000000000 : ℝ)*base66 + (6042718232638108321/415000000000000000000000000000000 : ℝ)*base67 + (1795231255241891679/415000000000000000000000000000000 : ℝ)*base70 + (4982840501378108321/415000000000000000000000000000000 : ℝ)*base71 + (34991488701157/6225000000000000000000000000 : ℝ)*base74 + (2373183840521891679/415000000000000000000000000000000 : ℝ)*base76 + (3022127355001891679/415000000000000000000000000000000 : ℝ)*base78 + (10959453290793108321/415000000000000000000000000000000 : ℝ)*base79 + (272297584249/194531250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (60303019/5000000000000000000000 : ℝ)*base90 + (60303019/5000000000000000000000 : ℝ)*base92 + (60303019/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1258_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1369/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1258_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1258_s5_0 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056260481/5000000000 : ℝ)*x 0 + (5392026023/10000000000 : ℝ)*x 1 + (5266361357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056260481/5000000000 : ℝ)^8451 ≤ (6424045265233/50000000000000 : ℝ)^6403 := by
    have hnat : (1056260481 : ℕ)^8451*50000000000000^6403 ≤ 6424045265233^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056260481 5000000000 6424045265233 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392026023/10000000000 : ℝ)^8451 ≤ (44254030549769/100000000000000 : ℝ)^6403 := by
    have hnat : (5392026023 : ℕ)^8451*100000000000000^6403 ≤ 44254030549769^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392026023 10000000000 44254030549769 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266361357/10000000000 : ℝ)^8451 ≤ (42897878903999/100000000000000 : ℝ)^6403 := by
    have hnat : (5266361357 : ℕ)^8451*100000000000000^6403 ≤ 42897878903999^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266361357 10000000000 42897878903999 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056260481/5000000000 : ℝ), (5392026023/10000000000 : ℝ), (5266361357/10000000000 : ℝ)] ![(6424045265233/50000000000000 : ℝ), (44254030549769/100000000000000 : ℝ), (42897878903999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056260481/5000000000 : ℝ)|^8451 ≤ (6424045265233/50000000000000 : ℝ)^6403
        have hw : |(-1056260481/5000000000 : ℝ)|=(1056260481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392026023/10000000000 : ℝ)|^8451 ≤ (44254030549769/100000000000000 : ℝ)^6403
        have hw : |(5392026023/10000000000 : ℝ)|=(5392026023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266361357/10000000000 : ℝ)|^8451 ≤ (42897878903999/100000000000000 : ℝ)^6403
        have hw : |(5266361357/10000000000 : ℝ)|=(5266361357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s5_1 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336127151/2500000000 : ℝ)*x 0 + (-136015519/625000000 : ℝ)*x 1 + (2633180707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336127151/2500000000 : ℝ)^8451 ≤ (43740028840609/100000000000000 : ℝ)^6403 := by
    have hnat : (1336127151 : ℕ)^8451*100000000000000^6403 ≤ 43740028840609^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336127151 2500000000 43740028840609 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136015519/625000000 : ℝ)^8451 ≤ (13362091626531/100000000000000 : ℝ)^6403 := by
    have hnat : (136015519 : ℕ)^8451*100000000000000^6403 ≤ 13362091626531^6403*625000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136015519 625000000 13362091626531 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633180707/5000000000 : ℝ)^8451 ≤ (5362234939601/12500000000000 : ℝ)^6403 := by
    have hnat : (2633180707 : ℕ)^8451*12500000000000^6403 ≤ 5362234939601^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633180707 5000000000 5362234939601 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336127151/2500000000 : ℝ), (-136015519/625000000 : ℝ), (2633180707/5000000000 : ℝ)] ![(43740028840609/100000000000000 : ℝ), (13362091626531/100000000000000 : ℝ), (5362234939601/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336127151/2500000000 : ℝ)|^8451 ≤ (43740028840609/100000000000000 : ℝ)^6403
        have hw : |(1336127151/2500000000 : ℝ)|=(1336127151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136015519/625000000 : ℝ)|^8451 ≤ (13362091626531/100000000000000 : ℝ)^6403
        have hw : |(-136015519/625000000 : ℝ)|=(136015519/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633180707/5000000000 : ℝ)|^8451 ≤ (5362234939601/12500000000000 : ℝ)^6403
        have hw : |(2633180707/5000000000 : ℝ)|=(2633180707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s5_2 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344509167/10000000000 : ℝ)*x 0 + (5266361299/10000000000 : ℝ)*x 1 + (-2176247707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344509167/10000000000 : ℝ)^8451 ≤ (43740034922019/100000000000000 : ℝ)^6403 := by
    have hnat : (5344509167 : ℕ)^8451*100000000000000^6403 ≤ 43740034922019^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344509167 10000000000 43740034922019 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266361299/10000000000 : ℝ)^8451 ≤ (1072446957011/2500000000000 : ℝ)^6403 := by
    have hnat : (5266361299 : ℕ)^8451*2500000000000^6403 ≤ 1072446957011^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266361299 10000000000 1072446957011 2500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2176247707/10000000000 : ℝ)^8451 ≤ (6681043394271/50000000000000 : ℝ)^6403 := by
    have hnat : (2176247707 : ℕ)^8451*50000000000000^6403 ≤ 6681043394271^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176247707 10000000000 6681043394271 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344509167/10000000000 : ℝ), (5266361299/10000000000 : ℝ), (-2176247707/10000000000 : ℝ)] ![(43740034922019/100000000000000 : ℝ), (1072446957011/2500000000000 : ℝ), (6681043394271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344509167/10000000000 : ℝ)|^8451 ≤ (43740034922019/100000000000000 : ℝ)^6403
        have hw : |(5344509167/10000000000 : ℝ)|=(5344509167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266361299/10000000000 : ℝ)|^8451 ≤ (1072446957011/2500000000000 : ℝ)^6403
        have hw : |(5266361299/10000000000 : ℝ)|=(5266361299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2176247707/10000000000 : ℝ)|^8451 ≤ (6681043394271/50000000000000 : ℝ)^6403
        have hw : |(-2176247707/10000000000 : ℝ)|=(2176247707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s5_3 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174263801/5000000000 : ℝ)*x 0 + (4222495293/10000000000 : ℝ)*x 1 + (2239100683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174263801/5000000000 : ℝ)^8451 ≤ (6663401218823/20000000000000 : ℝ)^6403 := by
    have hnat : (2174263801 : ℕ)^8451*20000000000000^6403 ≤ 6663401218823^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174263801 5000000000 6663401218823 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222495293/10000000000 : ℝ)^8451 ≤ (32048480854651/100000000000000 : ℝ)^6403 := by
    have hnat : (4222495293 : ℕ)^8451*100000000000000^6403 ≤ 32048480854651^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222495293 10000000000 32048480854651 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239100683/5000000000 : ℝ)^8451 ≤ (17317256518589/50000000000000 : ℝ)^6403 := by
    have hnat : (2239100683 : ℕ)^8451*50000000000000^6403 ≤ 17317256518589^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239100683 5000000000 17317256518589 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174263801/5000000000 : ℝ), (4222495293/10000000000 : ℝ), (2239100683/5000000000 : ℝ)] ![(6663401218823/20000000000000 : ℝ), (32048480854651/100000000000000 : ℝ), (17317256518589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174263801/5000000000 : ℝ)|^8451 ≤ (6663401218823/20000000000000 : ℝ)^6403
        have hw : |(2174263801/5000000000 : ℝ)|=(2174263801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222495293/10000000000 : ℝ)|^8451 ≤ (32048480854651/100000000000000 : ℝ)^6403
        have hw : |(4222495293/10000000000 : ℝ)|=(4222495293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2239100683/5000000000 : ℝ)|^8451 ≤ (17317256518589/50000000000000 : ℝ)^6403
        have hw : |(2239100683/5000000000 : ℝ)|=(2239100683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s5_4 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056262953/5000000000 : ℝ)*x 0 + (5266684199/10000000000 : ℝ)*x 1 + (5391701937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056262953/5000000000 : ℝ)^8451 ≤ (6424065108391/50000000000000 : ℝ)^6403 := by
    have hnat : (1056262953 : ℕ)^8451*50000000000000^6403 ≤ 6424065108391^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056262953 5000000000 6424065108391 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266684199/10000000000 : ℝ)^8451 ≤ (21450674909787/50000000000000 : ℝ)^6403 := by
    have hnat : (5266684199 : ℕ)^8451*50000000000000^6403 ≤ 21450674909787^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266684199 10000000000 21450674909787 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391701937/10000000000 : ℝ)^8451 ≤ (44250519948159/100000000000000 : ℝ)^6403 := by
    have hnat : (5391701937 : ℕ)^8451*100000000000000^6403 ≤ 44250519948159^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391701937 10000000000 44250519948159 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056262953/5000000000 : ℝ), (5266684199/10000000000 : ℝ), (5391701937/10000000000 : ℝ)] ![(6424065108391/50000000000000 : ℝ), (21450674909787/50000000000000 : ℝ), (44250519948159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056262953/5000000000 : ℝ)|^8451 ≤ (6424065108391/50000000000000 : ℝ)^6403
        have hw : |(-1056262953/5000000000 : ℝ)|=(1056262953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266684199/10000000000 : ℝ)|^8451 ≤ (21450674909787/50000000000000 : ℝ)^6403
        have hw : |(5266684199/10000000000 : ℝ)|=(5266684199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391701937/10000000000 : ℝ)|^8451 ≤ (44250519948159/100000000000000 : ℝ)^6403
        have hw : |(5391701937/10000000000 : ℝ)|=(5391701937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s5_5 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312410839/10000000000 : ℝ)*x 0 + (-41018149/200000000 : ℝ)*x 1 + (1078340389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312410839/10000000000 : ℝ)^8451 ≤ (43393648862389/100000000000000 : ℝ)^6403 := by
    have hnat : (5312410839 : ℕ)^8451*100000000000000^6403 ≤ 43393648862389^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312410839 10000000000 43393648862389 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41018149/200000000 : ℝ)^8451 ≤ (1544478885573/12500000000000 : ℝ)^6403 := by
    have hnat : (41018149 : ℕ)^8451*12500000000000^6403 ≤ 1544478885573^6403*200000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41018149 200000000 1544478885573 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078340389/2000000000 : ℝ)^8451 ≤ (44250520034817/100000000000000 : ℝ)^6403 := by
    have hnat : (1078340389 : ℕ)^8451*100000000000000^6403 ≤ 44250520034817^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078340389 2000000000 44250520034817 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312410839/10000000000 : ℝ), (-41018149/200000000 : ℝ), (1078340389/2000000000 : ℝ)] ![(43393648862389/100000000000000 : ℝ), (1544478885573/12500000000000 : ℝ), (44250520034817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312410839/10000000000 : ℝ)|^8451 ≤ (43393648862389/100000000000000 : ℝ)^6403
        have hw : |(5312410839/10000000000 : ℝ)|=(5312410839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41018149/200000000 : ℝ)|^8451 ≤ (1544478885573/12500000000000 : ℝ)^6403
        have hw : |(-41018149/200000000 : ℝ)|=(41018149/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078340389/2000000000 : ℝ)|^8451 ≤ (44250520034817/100000000000000 : ℝ)^6403
        have hw : |(1078340389/2000000000 : ℝ)|=(1078340389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s5_6 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312410821/10000000000 : ℝ)*x 0 + (2695850979/5000000000 : ℝ)*x 1 + (-2050907457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312410821/10000000000 : ℝ)^8451 ≤ (43393648668331/100000000000000 : ℝ)^6403 := by
    have hnat : (5312410821 : ℕ)^8451*100000000000000^6403 ≤ 43393648668331^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312410821 10000000000 43393648668331 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695850979/5000000000 : ℝ)^8451 ≤ (8850104035127/20000000000000 : ℝ)^6403 := by
    have hnat : (2695850979 : ℕ)^8451*20000000000000^6403 ≤ 8850104035127^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695850979 5000000000 8850104035127 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050907457/10000000000 : ℝ)^8451 ≤ (2471166228049/20000000000000 : ℝ)^6403 := by
    have hnat : (2050907457 : ℕ)^8451*20000000000000^6403 ≤ 2471166228049^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050907457 10000000000 2471166228049 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312410821/10000000000 : ℝ), (2695850979/5000000000 : ℝ), (-2050907457/10000000000 : ℝ)] ![(43393648668331/100000000000000 : ℝ), (8850104035127/20000000000000 : ℝ), (2471166228049/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312410821/10000000000 : ℝ)|^8451 ≤ (43393648668331/100000000000000 : ℝ)^6403
        have hw : |(5312410821/10000000000 : ℝ)|=(5312410821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695850979/5000000000 : ℝ)|^8451 ≤ (8850104035127/20000000000000 : ℝ)^6403
        have hw : |(2695850979/5000000000 : ℝ)|=(2695850979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2050907457/10000000000 : ℝ)|^8451 ≤ (2471166228049/20000000000000 : ℝ)^6403
        have hw : |(-2050907457/10000000000 : ℝ)|=(2050907457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_s5_7 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348537581/10000000000 : ℝ)*x 0 + (895509007/2000000000 : ℝ)*x 1 + (2111576989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348537581/10000000000 : ℝ)^8451 ≤ (1665855350221/5000000000000 : ℝ)^6403 := by
    have hnat : (4348537581 : ℕ)^8451*5000000000000^6403 ≤ 1665855350221^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348537581 10000000000 1665855350221 5000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895509007/2000000000 : ℝ)^8451 ≤ (6925562706159/20000000000000 : ℝ)^6403 := by
    have hnat : (895509007 : ℕ)^8451*20000000000000^6403 ≤ 6925562706159^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895509007 2000000000 6925562706159 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111576989/5000000000 : ℝ)^8451 ≤ (32055079449769/100000000000000 : ℝ)^6403 := by
    have hnat : (2111576989 : ℕ)^8451*100000000000000^6403 ≤ 32055079449769^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111576989 5000000000 32055079449769 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348537581/10000000000 : ℝ), (895509007/2000000000 : ℝ), (2111576989/5000000000 : ℝ)] ![(1665855350221/5000000000000 : ℝ), (6925562706159/20000000000000 : ℝ), (32055079449769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348537581/10000000000 : ℝ)|^8451 ≤ (1665855350221/5000000000000 : ℝ)^6403
        have hw : |(4348537581/10000000000 : ℝ)|=(4348537581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895509007/2000000000 : ℝ)|^8451 ≤ (6925562706159/20000000000000 : ℝ)^6403
        have hw : |(895509007/2000000000 : ℝ)|=(895509007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111576989/5000000000 : ℝ)|^8451 ≤ (32055079449769/100000000000000 : ℝ)^6403
        have hw : |(2111576989/5000000000 : ℝ)|=(2111576989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1258_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (459/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14137/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5689/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5689/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5689/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5689/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5689/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5689/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5689/50000 : ℝ) ^ (4225/1024 : ℝ) ≤ (3186325630249083/25000000000000000000 : ℝ) := by
    have hpowers : (5689/50000 : ℝ)^4225 ≤ (3186325630249083/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5689 : ℕ)^4225*25000000000000000000^1024 ≤ 3186325630249083^1024*50000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5689 50000 3186325630249083 25000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5689/50000 : ℝ)) (X := (3186325630249083/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (4225/1024 : ℝ) ≤ (16073867067330367/50000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^4225 ≤ (16073867067330367/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7119 : ℕ)^4225*50000000000000000000^1024 ≤ 16073867067330367^1024*50000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 16073867067330367 50000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (16073867067330367/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503186325630249083/12500000000000000000 : ℝ) ≤ (10000617748152067/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (12503186325630249083/12500000000000000000 : ℝ)^1024 ≤ (10000617748152067/10000000000000000 : ℝ)^4225 := by
      have hnat : (12503186325630249083 : ℕ)^1024*10000000000000000^4225 ≤ 10000617748152067^4225*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503186325630249083 12500000000000000000 10000617748152067 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000617748152067/10000000000000000 : ℝ)) (X := (12503186325630249083/12500000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022446518327828533/50000000000000000000 : ℝ) ≤ (2500271968365379/2500000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (50022446518327828533/50000000000000000000 : ℝ)^1024 ≤ (2500271968365379/2500000000000000 : ℝ)^4225 := by
      have hnat : (50022446518327828533 : ℕ)^1024*2500000000000000^4225 ≤ 2500271968365379^4225*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022446518327828533 50000000000000000000 2500271968365379 2500000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500271968365379/2500000000000000 : ℝ)) (X := (50022446518327828533/50000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016073867067330367/25000000000000000000 : ℝ) ≤ (2000311599754193/2000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (25016073867067330367/25000000000000000000 : ℝ)^1024 ≤ (2000311599754193/2000000000000000 : ℝ)^4225 := by
      have hnat : (25016073867067330367 : ℕ)^1024*2000000000000000^4225 ≤ 2000311599754193^4225*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016073867067330367 25000000000000000000 2000311599754193 2000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000311599754193/2000000000000000 : ℝ)) (X := (25016073867067330367/25000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3186325630249083/25000000000000000000 : ℝ) ≤ ((223367723345102267/223437500000000000 : ℝ)+2*(470125309449/286000000000000 : ℝ)*(5689/50000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (223367723345102267/223437500000000000 : ℝ)+2*(470125309449/286000000000000 : ℝ)*(5689/50000 : ℝ)=(10000617748152067/10000000000000000 : ℝ) by norm_num, show 1+2*(3186325630249083/25000000000000000000 : ℝ)=(12503186325630249083/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16073867067330367/50000000000000000000 : ℝ)+(3186325630249083/25000000000000000000 : ℝ) ≤ ((223367723345102267/223437500000000000 : ℝ)+(470125309449/286000000000000 : ℝ)*((7119/50000 : ℝ)+(5689/50000 : ℝ)))^(4225/1024 : ℝ) := by
    rw [show (223367723345102267/223437500000000000 : ℝ)+(470125309449/286000000000000 : ℝ)*((7119/50000 : ℝ)+(5689/50000 : ℝ))=(2500271968365379/2500000000000000 : ℝ) by norm_num, show 1+(16073867067330367/50000000000000000000 : ℝ)+(3186325630249083/25000000000000000000 : ℝ)=(50022446518327828533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16073867067330367/50000000000000000000 : ℝ) ≤ ((223367723345102267/223437500000000000 : ℝ)+2*(470125309449/286000000000000 : ℝ)*(7119/50000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (223367723345102267/223437500000000000 : ℝ)+2*(470125309449/286000000000000 : ℝ)*(7119/50000 : ℝ)=(2000311599754193/2000000000000000 : ℝ) by norm_num, show 1+2*(16073867067330367/50000000000000000000 : ℝ)=(25016073867067330367/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (223367723345102267/223437500000000000 : ℝ)*(X 1 0+X 2 0)+(470125309449/286000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (223367723345102267/223437500000000000 : ℝ)) (alpha := (470125309449/286000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (223367723345102267/223437500000000000 : ℝ)*(X 0 1+X 2 1)+(470125309449/286000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (223367723345102267/223437500000000000 : ℝ)) (alpha := (470125309449/286000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (223367723345102267/223437500000000000 : ℝ)*(X 0 2+X 1 2)+(470125309449/286000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (5689/50000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (223367723345102267/223437500000000000 : ℝ)) (alpha := (470125309449/286000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056260481/5000000000 : ℝ)*X 0 0+(5392026023/10000000000 : ℝ)*X 0 1+(5266361357/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336127151/2500000000 : ℝ)*X 1 0+(-136015519/625000000 : ℝ)*X 1 1+(2633180707/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344509167/10000000000 : ℝ)*X 2 0+(5266361299/10000000000 : ℝ)*X 2 1+(-2176247707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174263801/5000000000 : ℝ)*X 0 0+(4222495293/10000000000 : ℝ)*X 0 1+(2239100683/5000000000 : ℝ)*X 0 2+(2174263801/5000000000 : ℝ)*X 1 0+(4222495293/10000000000 : ℝ)*X 1 1+(2239100683/5000000000 : ℝ)*X 1 2+(2174263801/5000000000 : ℝ)*X 2 0+(4222495293/10000000000 : ℝ)*X 2 1+(2239100683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1056262953/5000000000 : ℝ)*X 0 0+(5266684199/10000000000 : ℝ)*X 0 1+(5391701937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312410839/10000000000 : ℝ)*X 1 0+(-41018149/200000000 : ℝ)*X 1 1+(1078340389/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312410821/10000000000 : ℝ)*X 2 0+(2695850979/5000000000 : ℝ)*X 2 1+(-2050907457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348537581/10000000000 : ℝ)*X 0 0+(895509007/2000000000 : ℝ)*X 0 1+(2111576989/5000000000 : ℝ)*X 0 2+(4348537581/10000000000 : ℝ)*X 1 0+(895509007/2000000000 : ℝ)*X 1 1+(2111576989/5000000000 : ℝ)*X 1 2+(4348537581/10000000000 : ℝ)*X 2 0+(895509007/2000000000 : ℝ)*X 2 1+(2111576989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18083296008519877503382923/5585937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3045467/3125000000000 : ℝ)*(base19) + (1100187403/100000000000000 : ℝ)*(base23) + (5564503/12500000000000 : ℝ)*(lower2) + (11061387/20000000000000 : ℝ)*(upper5) + (1483566003849199/25000000000000 : ℝ)*(major0) + (1483566003849199/25000000000000 : ℝ)*(major1) + (1483566003849199/25000000000000 : ℝ)*(major2) + (7957719615439331/100000000000000 : ℝ)*(sp0) + (7957726817354217/100000000000000 : ℝ)*(sp1) + (1989441766286567/25000000000000 : ℝ)*(sp2) + (122210860781299/3125000000000 : ℝ)*(sp3) + (2427494717/5000000000000 : ℝ)*(sp4) + (4125052451/10000000000000 : ℝ)*(sp5) + (6106274351/50000000000000 : ℝ)*(sp7) + (391075975755027/10000000000000 : ℝ)*(f.failure) + (7957768165333671/100000000000000 : ℝ)*(f.sum) + (14772317005151/3575000000000000000000000000 : ℝ)*base65 + (108573224882422843/22343750000000000000000000000000 : ℝ)*base68 + (357897946153047843/22343750000000000000000000000000 : ℝ)*base70 + (31644118253983407/22343750000000000000000000000000 : ℝ)*base71 + (8402399200901/3575000000000000000000000000 : ℝ)*base73 + (343072556131641593/22343750000000000000000000000000 : ℝ)*base76 + (77627807857579093/22343750000000000000000000000000 : ℝ)*base78 + (145201772955545907/22343750000000000000000000000000 : ℝ)*base79 + (8789019570751/3575000000000000000000000000 : ℝ)*base81 + (1648271/1000000000000000000000 : ℝ)*base89 + (1648271/1000000000000000000000 : ℝ)*base91 + (1648271/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (180242136104005412205711399/22343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1522880417/100000000000000 : ℝ)*(base19) + (798678829/50000000000000 : ℝ)*(base23) + (1379119/800000000000 : ℝ)*(upper3) + (11677663/25000000000000 : ℝ)*(lower4) + (163598357/100000000000000 : ℝ)*(upper5) + (2982454647887353/50000000000000 : ℝ)*(major0) + (2982454647887353/50000000000000 : ℝ)*(major1) + (2982454647887353/50000000000000 : ℝ)*(major2) + (5343422199/12500000000000 : ℝ)*(sp1) + (4500611841/10000000000000 : ℝ)*(sp2) + (7998862913387897/100000000000000 : ℝ)*(sp4) + (7998818643129889/100000000000000 : ℝ)*(sp5) + (799881630991183/10000000000000 : ℝ)*(sp6) + (1965477704634401/50000000000000 : ℝ)*(sp7) + (1965477704634401/50000000000000 : ℝ)*(f.failure) + (7998862913387897/100000000000000 : ℝ)*(f.sum) + (22144472703503/7150000000000000000000000000 : ℝ)*base66 + (103197641388082629/44687500000000000000000000000000 : ℝ)*base67 + (336331326704417371/44687500000000000000000000000000 : ℝ)*base70 + (311452256238167371/44687500000000000000000000000000 : ℝ)*base72 + (70221852976697/7150000000000000000000000000 : ℝ)*base73 + (1056636300664417371/44687500000000000000000000000000 : ℝ)*base76 + (65273665589104871/44687500000000000000000000000000 : ℝ)*base78 + (1173347191880979871/44687500000000000000000000000000 : ℝ)*base80 + (58245809440097/7150000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (48586827/5000000000000000000000 : ℝ)*base90 + (48586827/5000000000000000000000 : ℝ)*base92 + (48586827/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1258_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1258_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1258_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8091/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2391/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1258_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1258_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1258_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8091/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2391/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1258_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
