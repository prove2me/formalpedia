-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1179_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:49:11.943149+00:00
-- url     : https://prove2.me/submissions/783639f6-3018-4355-a83e-f094436ecd03

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
theorem support_rectangle_w1179_s3_0 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-536475203/2500000000 : ℝ)*x 0 + (2712739749/5000000000 : ℝ)*x 1 + (1308859277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536475203/2500000000 : ℝ)^2093 ≤ (13036299312457/100000000000000 : ℝ)^1581 := by
    have hnat : (536475203 : ℕ)^2093*100000000000000^1581 ≤ 13036299312457^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536475203 2500000000 13036299312457 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712739749/5000000000 : ℝ)^2093 ≤ (44507896004609/100000000000000 : ℝ)^1581 := by
    have hnat : (2712739749 : ℕ)^2093*100000000000000^1581 ≤ 44507896004609^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712739749 5000000000 44507896004609 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308859277/2500000000 : ℝ)^2093 ≤ (21227902330061/50000000000000 : ℝ)^1581 := by
    have hnat : (1308859277 : ℕ)^2093*50000000000000^1581 ≤ 21227902330061^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308859277 2500000000 21227902330061 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-536475203/2500000000 : ℝ), (2712739749/5000000000 : ℝ), (1308859277/2500000000 : ℝ)] ![(13036299312457/100000000000000 : ℝ), (44507896004609/100000000000000 : ℝ), (21227902330061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-536475203/2500000000 : ℝ)|^2093 ≤ (13036299312457/100000000000000 : ℝ)^1581
        have hw : |(-536475203/2500000000 : ℝ)|=(536475203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712739749/5000000000 : ℝ)|^2093 ≤ (44507896004609/100000000000000 : ℝ)^1581
        have hw : |(2712739749/5000000000 : ℝ)|=(2712739749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308859277/2500000000 : ℝ)|^2093 ≤ (21227902330061/50000000000000 : ℝ)^1581
        have hw : |(1308859277/2500000000 : ℝ)|=(1308859277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s3_1 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5352919333/10000000000 : ℝ)*x 0 + (-2242967807/10000000000 : ℝ)*x 1 + (327214807/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352919333/10000000000 : ℝ)^2093 ≤ (341574941643/781250000000 : ℝ)^1581 := by
    have hnat : (5352919333 : ℕ)^2093*781250000000^1581 ≤ 341574941643^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352919333 10000000000 341574941643 781250000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242967807/10000000000 : ℝ)^2093 ≤ (431956403171/3125000000000 : ℝ)^1581 := by
    have hnat : (2242967807 : ℕ)^2093*3125000000000^1581 ≤ 431956403171^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242967807 10000000000 431956403171 3125000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327214807/625000000 : ℝ)^2093 ≤ (663371914937/1562500000000 : ℝ)^1581 := by
    have hnat : (327214807 : ℕ)^2093*1562500000000^1581 ≤ 663371914937^1581*625000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327214807 625000000 663371914937 1562500000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352919333/10000000000 : ℝ), (-2242967807/10000000000 : ℝ), (327214807/625000000 : ℝ)] ![(341574941643/781250000000 : ℝ), (431956403171/3125000000000 : ℝ), (663371914937/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352919333/10000000000 : ℝ)|^2093 ≤ (341574941643/781250000000 : ℝ)^1581
        have hw : |(5352919333/10000000000 : ℝ)|=(5352919333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2242967807/10000000000 : ℝ)|^2093 ≤ (431956403171/3125000000000 : ℝ)^1581
        have hw : |(-2242967807/10000000000 : ℝ)|=(2242967807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327214807/625000000 : ℝ)|^2093 ≤ (663371914937/1562500000000 : ℝ)^1581
        have hw : |(327214807/625000000 : ℝ)|=(327214807/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s3_2 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5352919421/10000000000 : ℝ)*x 0 + (1308859221/2500000000 : ℝ)*x 1 + (-2242967727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352919421/10000000000 : ℝ)^2093 ≤ (546519918523/1250000000000 : ℝ)^1581 := by
    have hnat : (5352919421 : ℕ)^2093*1250000000000^1581 ≤ 546519918523^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352919421 10000000000 546519918523 1250000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308859221/2500000000 : ℝ)^2093 ≤ (21227901127687/50000000000000 : ℝ)^1581 := by
    have hnat : (1308859221 : ℕ)^2093*50000000000000^1581 ≤ 21227901127687^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308859221 2500000000 21227901127687 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242967727/10000000000 : ℝ)^2093 ≤ (13822604248801/100000000000000 : ℝ)^1581 := by
    have hnat : (2242967727 : ℕ)^2093*100000000000000^1581 ≤ 13822604248801^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242967727 10000000000 13822604248801 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352919421/10000000000 : ℝ), (1308859221/2500000000 : ℝ), (-2242967727/10000000000 : ℝ)] ![(546519918523/1250000000000 : ℝ), (21227901127687/50000000000000 : ℝ), (13822604248801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352919421/10000000000 : ℝ)|^2093 ≤ (546519918523/1250000000000 : ℝ)^1581
        have hw : |(5352919421/10000000000 : ℝ)|=(5352919421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308859221/2500000000 : ℝ)|^2093 ≤ (21227901127687/50000000000000 : ℝ)^1581
        have hw : |(1308859221/2500000000 : ℝ)|=(1308859221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2242967727/10000000000 : ℝ)|^2093 ≤ (13822604248801/100000000000000 : ℝ)^1581
        have hw : |(-2242967727/10000000000 : ℝ)|=(2242967727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s3_3 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2178726981/5000000000 : ℝ)*x 0 + (4171138007/10000000000 : ℝ)*x 1 + (2275984177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178726981/5000000000 : ℝ)^2093 ≤ (16648301005303/50000000000000 : ℝ)^1581 := by
    have hnat : (2178726981 : ℕ)^2093*50000000000000^1581 ≤ 16648301005303^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178726981 5000000000 16648301005303 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171138007/10000000000 : ℝ)^2093 ≤ (31425025846369/100000000000000 : ℝ)^1581 := by
    have hnat : (4171138007 : ℕ)^2093*100000000000000^1581 ≤ 31425025846369^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171138007 10000000000 31425025846369 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2275984177/5000000000 : ℝ)^2093 ≤ (17639186064087/50000000000000 : ℝ)^1581 := by
    have hnat : (2275984177 : ℕ)^2093*50000000000000^1581 ≤ 17639186064087^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275984177 5000000000 17639186064087 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178726981/5000000000 : ℝ), (4171138007/10000000000 : ℝ), (2275984177/5000000000 : ℝ)] ![(16648301005303/50000000000000 : ℝ), (31425025846369/100000000000000 : ℝ), (17639186064087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178726981/5000000000 : ℝ)|^2093 ≤ (16648301005303/50000000000000 : ℝ)^1581
        have hw : |(2178726981/5000000000 : ℝ)|=(2178726981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171138007/10000000000 : ℝ)|^2093 ≤ (31425025846369/100000000000000 : ℝ)^1581
        have hw : |(4171138007/10000000000 : ℝ)|=(4171138007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2275984177/5000000000 : ℝ)|^2093 ≤ (17639186064087/50000000000000 : ℝ)^1581
        have hw : |(2275984177/5000000000 : ℝ)|=(2275984177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s3_4 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145917119/10000000000 : ℝ)*x 0 + (2618078007/5000000000 : ℝ)*x 1 + (5424756739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145917119/10000000000 : ℝ)^2093 ≤ (13036430458939/100000000000000 : ℝ)^1581 := by
    have hnat : (2145917119 : ℕ)^2093*100000000000000^1581 ≤ 13036430458939^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145917119 10000000000 13036430458939 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618078007/5000000000 : ℝ)^2093 ≤ (2653970164567/6250000000000 : ℝ)^1581 := by
    have hnat : (2618078007 : ℕ)^2093*6250000000000^1581 ≤ 2653970164567^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618078007 5000000000 2653970164567 6250000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424756739/10000000000 : ℝ)^2093 ≤ (44500046894233/100000000000000 : ℝ)^1581 := by
    have hnat : (5424756739 : ℕ)^2093*100000000000000^1581 ≤ 44500046894233^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424756739 10000000000 44500046894233 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145917119/10000000000 : ℝ), (2618078007/5000000000 : ℝ), (5424756739/10000000000 : ℝ)] ![(13036430458939/100000000000000 : ℝ), (2653970164567/6250000000000 : ℝ), (44500046894233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145917119/10000000000 : ℝ)|^2093 ≤ (13036430458939/100000000000000 : ℝ)^1581
        have hw : |(-2145917119/10000000000 : ℝ)|=(2145917119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618078007/5000000000 : ℝ)|^2093 ≤ (2653970164567/6250000000000 : ℝ)^1581
        have hw : |(2618078007/5000000000 : ℝ)|=(2618078007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424756739/10000000000 : ℝ)|^2093 ≤ (44500046894233/100000000000000 : ℝ)^1581
        have hw : |(5424756739/10000000000 : ℝ)|=(5424756739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s3_5 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663080537/1250000000 : ℝ)*x 0 + (-2053648563/10000000000 : ℝ)*x 1 + (2712378317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663080537/1250000000 : ℝ)^2093 ≤ (43200362666199/100000000000000 : ℝ)^1581 := by
    have hnat : (663080537 : ℕ)^2093*100000000000000^1581 ≤ 43200362666199^1581*1250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663080537 1250000000 43200362666199 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2053648563/10000000000 : ℝ)^2093 ≤ (1537448945811/12500000000000 : ℝ)^1581 := by
    have hnat : (2053648563 : ℕ)^2093*12500000000000^1581 ≤ 1537448945811^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053648563 10000000000 1537448945811 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712378317/5000000000 : ℝ)^2093 ≤ (8900009150793/20000000000000 : ℝ)^1581 := by
    have hnat : (2712378317 : ℕ)^2093*20000000000000^1581 ≤ 8900009150793^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712378317 5000000000 8900009150793 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663080537/1250000000 : ℝ), (-2053648563/10000000000 : ℝ), (2712378317/5000000000 : ℝ)] ![(43200362666199/100000000000000 : ℝ), (1537448945811/12500000000000 : ℝ), (8900009150793/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663080537/1250000000 : ℝ)|^2093 ≤ (43200362666199/100000000000000 : ℝ)^1581
        have hw : |(663080537/1250000000 : ℝ)|=(663080537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2053648563/10000000000 : ℝ)|^2093 ≤ (1537448945811/12500000000000 : ℝ)^1581
        have hw : |(-2053648563/10000000000 : ℝ)|=(2053648563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712378317/5000000000 : ℝ)|^2093 ≤ (8900009150793/20000000000000 : ℝ)^1581
        have hw : |(2712378317/5000000000 : ℝ)|=(2712378317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s3_6 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304645379/10000000000 : ℝ)*x 0 + (542475561/1000000000 : ℝ)*x 1 + (-2053648493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304645379/10000000000 : ℝ)^2093 ≤ (10800093585569/25000000000000 : ℝ)^1581 := by
    have hnat : (5304645379 : ℕ)^2093*25000000000000^1581 ≤ 10800093585569^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304645379 10000000000 10800093585569 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542475561/1000000000 : ℝ)^2093 ≤ (1112500865841/2500000000000 : ℝ)^1581 := by
    have hnat : (542475561 : ℕ)^2093*2500000000000^1581 ≤ 1112500865841^1581*1000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542475561 1000000000 1112500865841 2500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2053648493/10000000000 : ℝ)^2093 ≤ (12299591011479/100000000000000 : ℝ)^1581 := by
    have hnat : (2053648493 : ℕ)^2093*100000000000000^1581 ≤ 12299591011479^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053648493 10000000000 12299591011479 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304645379/10000000000 : ℝ), (542475561/1000000000 : ℝ), (-2053648493/10000000000 : ℝ)] ![(10800093585569/25000000000000 : ℝ), (1112500865841/2500000000000 : ℝ), (12299591011479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304645379/10000000000 : ℝ)|^2093 ≤ (10800093585569/25000000000000 : ℝ)^1581
        have hw : |(5304645379/10000000000 : ℝ)|=(5304645379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542475561/1000000000 : ℝ)|^2093 ≤ (1112500865841/2500000000000 : ℝ)^1581
        have hw : |(542475561/1000000000 : ℝ)|=(542475561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2053648493/10000000000 : ℝ)|^2093 ≤ (12299591011479/100000000000000 : ℝ)^1581
        have hw : |(-2053648493/10000000000 : ℝ)|=(2053648493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s3_7 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (136171449/312500000 : ℝ)*x 0 + (56881601/125000000 : ℝ)*x 1 + (417258659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136171449/312500000 : ℝ)^2093 ≤ (3329692982681/10000000000000 : ℝ)^1581 := by
    have hnat : (136171449 : ℕ)^2093*10000000000000^1581 ≤ 3329692982681^1581*312500000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136171449 312500000 3329692982681 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56881601/125000000 : ℝ)^2093 ≤ (282108765583/800000000000 : ℝ)^1581 := by
    have hnat : (56881601 : ℕ)^2093*800000000000^1581 ≤ 282108765583^1581*125000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56881601 125000000 282108765583 800000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417258659/1000000000 : ℝ)^2093 ≤ (785986861557/2500000000000 : ℝ)^1581 := by
    have hnat : (417258659 : ℕ)^2093*2500000000000^1581 ≤ 785986861557^1581*1000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417258659 1000000000 785986861557 2500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136171449/312500000 : ℝ), (56881601/125000000 : ℝ), (417258659/1000000000 : ℝ)] ![(3329692982681/10000000000000 : ℝ), (282108765583/800000000000 : ℝ), (785986861557/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136171449/312500000 : ℝ)|^2093 ≤ (3329692982681/10000000000000 : ℝ)^1581
        have hw : |(136171449/312500000 : ℝ)|=(136171449/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56881601/125000000 : ℝ)|^2093 ≤ (282108765583/800000000000 : ℝ)^1581
        have hw : |(56881601/125000000 : ℝ)|=(56881601/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(417258659/1000000000 : ℝ)|^2093 ≤ (785986861557/2500000000000 : ℝ)^1581
        have hw : |(417258659/1000000000 : ℝ)|=(417258659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1179_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3279/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5371/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3691/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3279/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3279/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3279/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3279/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3279/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3279/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4617/50000 : ℝ) ^ (8371/2048 : ℝ) ≤ (1180761342970419/20000000000000000000 : ℝ) := by
    have hpowers : (4617/50000 : ℝ)^8371 ≤ (1180761342970419/20000000000000000000 : ℝ)^2048 := by
      have hnat : (4617 : ℕ)^8371*20000000000000000000^2048 ≤ 1180761342970419^2048*50000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4617 50000 1180761342970419 20000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4617/50000 : ℝ)) (X := (1180761342970419/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3279/20000 : ℝ) ^ (8371/2048 : ℝ) ≤ (61689268671430887/100000000000000000000 : ℝ) := by
    have hpowers : (3279/20000 : ℝ)^8371 ≤ (61689268671430887/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3279 : ℕ)^8371*100000000000000000000^2048 ≤ 61689268671430887^2048*20000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3279 20000 61689268671430887 100000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3279/20000 : ℝ)) (X := (61689268671430887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001180761342970419/10000000000000000000 : ℝ) ≤ (5000144432648447/5000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (10001180761342970419/10000000000000000000 : ℝ)^2048 ≤ (5000144432648447/5000000000000000 : ℝ)^8371 := by
      have hnat : (10001180761342970419 : ℕ)^2048*5000000000000000^8371 ≤ 5000144432648447^8371*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001180761342970419 10000000000000000000 5000144432648447 5000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000144432648447/5000000000000000 : ℝ)) (X := (10001180761342970419/10000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50033796537693141491/50000000000000000000 : ℝ) ≤ (1250206658842567/1250000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (50033796537693141491/50000000000000000000 : ℝ)^2048 ≤ (1250206658842567/1250000000000000 : ℝ)^8371 := by
      have hnat : (50033796537693141491 : ℕ)^2048*1250000000000000^8371 ≤ 1250206658842567^8371*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033796537693141491 50000000000000000000 1250206658842567 1250000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250206658842567/1250000000000000 : ℝ)) (X := (50033796537693141491/50000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50061689268671430887/50000000000000000000 : ℝ) ≤ (5001508838092089/5000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (50061689268671430887/50000000000000000000 : ℝ)^2048 ≤ (5001508838092089/5000000000000000 : ℝ)^8371 := by
      have hnat : (50061689268671430887 : ℕ)^2048*5000000000000000^8371 ≤ 5001508838092089^8371*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50061689268671430887 50000000000000000000 5001508838092089 5000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001508838092089/5000000000000000 : ℝ)) (X := (50061689268671430887/50000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1180761342970419/20000000000000000000 : ℝ) ≤ ((11931145120776312913/11935000000000000000 : ℝ)+2*(682202721821/358050000000000 : ℝ)*(4617/50000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (11931145120776312913/11935000000000000000 : ℝ)+2*(682202721821/358050000000000 : ℝ)*(4617/50000 : ℝ)=(5000144432648447/5000000000000000 : ℝ) by norm_num, show 1+2*(1180761342970419/20000000000000000000 : ℝ)=(10001180761342970419/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(61689268671430887/100000000000000000000 : ℝ)+(1180761342970419/20000000000000000000 : ℝ) ≤ ((11931145120776312913/11935000000000000000 : ℝ)+(682202721821/358050000000000 : ℝ)*((3279/20000 : ℝ)+(4617/50000 : ℝ)))^(8371/2048 : ℝ) := by
    rw [show (11931145120776312913/11935000000000000000 : ℝ)+(682202721821/358050000000000 : ℝ)*((3279/20000 : ℝ)+(4617/50000 : ℝ))=(1250206658842567/1250000000000000 : ℝ) by norm_num, show 1+(61689268671430887/100000000000000000000 : ℝ)+(1180761342970419/20000000000000000000 : ℝ)=(50033796537693141491/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(61689268671430887/100000000000000000000 : ℝ) ≤ ((11931145120776312913/11935000000000000000 : ℝ)+2*(682202721821/358050000000000 : ℝ)*(3279/20000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (11931145120776312913/11935000000000000000 : ℝ)+2*(682202721821/358050000000000 : ℝ)*(3279/20000 : ℝ)=(5001508838092089/5000000000000000 : ℝ) by norm_num, show 1+2*(61689268671430887/100000000000000000000 : ℝ)=(50061689268671430887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11931145120776312913/11935000000000000000 : ℝ)*(X 1 0+X 2 0)+(682202721821/358050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (4617/50000 : ℝ)) (hi := (3279/20000 : ℝ)) (c := (11931145120776312913/11935000000000000000 : ℝ)) (alpha := (682202721821/358050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11931145120776312913/11935000000000000000 : ℝ)*(X 0 1+X 2 1)+(682202721821/358050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (4617/50000 : ℝ)) (hi := (3279/20000 : ℝ)) (c := (11931145120776312913/11935000000000000000 : ℝ)) (alpha := (682202721821/358050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11931145120776312913/11935000000000000000 : ℝ)*(X 0 2+X 1 2)+(682202721821/358050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (4617/50000 : ℝ)) (hi := (3279/20000 : ℝ)) (c := (11931145120776312913/11935000000000000000 : ℝ)) (alpha := (682202721821/358050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-536475203/2500000000 : ℝ)*X 0 0+(2712739749/5000000000 : ℝ)*X 0 1+(1308859277/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352919333/10000000000 : ℝ)*X 1 0+(-2242967807/10000000000 : ℝ)*X 1 1+(327214807/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352919421/10000000000 : ℝ)*X 2 0+(1308859221/2500000000 : ℝ)*X 2 1+(-2242967727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178726981/5000000000 : ℝ)*X 0 0+(4171138007/10000000000 : ℝ)*X 0 1+(2275984177/5000000000 : ℝ)*X 0 2+(2178726981/5000000000 : ℝ)*X 1 0+(4171138007/10000000000 : ℝ)*X 1 1+(2275984177/5000000000 : ℝ)*X 1 2+(2178726981/5000000000 : ℝ)*X 2 0+(4171138007/10000000000 : ℝ)*X 2 1+(2275984177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2145917119/10000000000 : ℝ)*X 0 0+(2618078007/5000000000 : ℝ)*X 0 1+(5424756739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663080537/1250000000 : ℝ)*X 1 0+(-2053648563/10000000000 : ℝ)*X 1 1+(2712378317/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304645379/10000000000 : ℝ)*X 2 0+(542475561/1000000000 : ℝ)*X 2 1+(-2053648493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136171449/312500000 : ℝ)*X 0 0+(56881601/125000000 : ℝ)*X 0 1+(417258659/1000000000 : ℝ)*X 0 2+(136171449/312500000 : ℝ)*X 1 0+(56881601/125000000 : ℝ)*X 1 1+(417258659/1000000000 : ℝ)*X 1 2+(136171449/312500000 : ℝ)*X 2 0+(56881601/125000000 : ℝ)*X 2 1+(417258659/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22923939086438735215341/5967500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1025155499/100000000000000 : ℝ)*(base19) + (102439967/10000000000000 : ℝ)*(base23) + (23355151/50000000000000 : ℝ)*(lower2) + (74805767/100000000000000 : ℝ)*(upper3) + (4482383/4000000000000 : ℝ)*(upper5) + (1971967688989059/50000000000000 : ℝ)*(major0) + (1971967688989059/50000000000000 : ℝ)*(major1) + (1971967688989059/50000000000000 : ℝ)*(major2) + (5261997440357173/100000000000000 : ℝ)*(sp0) + (10524025632133/200000000000 : ℝ)*(sp1) + (526201281682233/10000000000000 : ℝ)*(sp2) + (1312924440920477/50000000000000 : ℝ)*(sp3) + (8200432413/50000000000000 : ℝ)*(sp4) + (7904844459/100000000000000 : ℝ)*(sp7) + (1312928393342707/50000000000000 : ℝ)*(f.failure) + (5262013841221999/100000000000000 : ℝ)*(f.sum) + (43689069399051/5967500000000000000000000000 : ℝ)*base65 + (100554690870519897/54250000000000000000000000000000 : ℝ)*base67 + (201897875188480103/54250000000000000000000000000000 : ℝ)*base70 + (532390314766480103/54250000000000000000000000000000 : ℝ)*base72 + (33458578311311/5967500000000000000000000000 : ℝ)*base73 + (331004762628019897/54250000000000000000000000000000 : ℝ)*base75 + (798205898593980103/54250000000000000000000000000000 : ℝ)*base78 + (166353593512019897/54250000000000000000000000000000 : ℝ)*base79 + (9430592918323/2983750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (14247369/2500000000000000000000 : ℝ)*base89 + (14247369/2500000000000000000000 : ℝ)*base91 + (14247369/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40121542563446445810357901/3875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1321101833/100000000000000 : ℝ)*(base19) + (2524610667/100000000000000 : ℝ)*(base23) + (167232283/100000000000000 : ℝ)*(upper3) + (5370621/25000000000000 : ℝ)*(lower4) + (1133997/1000000000000 : ℝ)*(upper5) + (3974064616551557/100000000000000 : ℝ)*(major0) + (3974064616551557/100000000000000 : ℝ)*(major1) + (3974064616551557/100000000000000 : ℝ)*(major2) + (20152719659/100000000000000 : ℝ)*(sp1) + (7249971263/25000000000000 : ℝ)*(sp2) + (5302212171798589/100000000000000 : ℝ)*(sp4) + (5302190697977097/100000000000000 : ℝ)*(sp5) + (530218064730287/10000000000000 : ℝ)*(sp6) + (661479179043243/25000000000000 : ℝ)*(sp7) + (661479179043243/25000000000000 : ℝ)*(f.failure) + (5302212171798589/100000000000000 : ℝ)*(f.sum) + (5786725880779/3255000000000000000000000000 : ℝ)*base65 + (11145464205930307/325500000000000000000000000000000 : ℝ)*base68 + (1988053159296569693/325500000000000000000000000000000 : ℝ)*base69 + (667071592944569693/325500000000000000000000000000000 : ℝ)*base71 + (4741920193187/1627500000000000000000000000 : ℝ)*base73 + (93961096304069693/325500000000000000000000000000000 : ℝ)*base75 + (1237550554238069693/325500000000000000000000000000000 : ℝ)*base77 + (1481729551433069693/325500000000000000000000000000000 : ℝ)*base79 + (3247548335431/813750000000000000000000000 : ℝ)*base81 + (3788719/1250000000000000000000 : ℝ)*base90 + (3788719/1250000000000000000000 : ℝ)*base92 + (3788719/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1179_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3279/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1179_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1179_s4_0 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074308389/5000000000 : ℝ)*x 0 + (5400179403/10000000000 : ℝ)*x 1 + (82171243/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074308389/5000000000 : ℝ)^2093 ≤ (13058146489873/100000000000000 : ℝ)^1581 := by
    have hnat : (1074308389 : ℕ)^2093*100000000000000^1581 ≤ 13058146489873^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074308389 5000000000 13058146489873 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400179403/10000000000 : ℝ)^2093 ≤ (11058335141281/25000000000000 : ℝ)^1581 := by
    have hnat : (5400179403 : ℕ)^2093*25000000000000^1581 ≤ 11058335141281^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400179403 10000000000 11058335141281 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82171243/156250000 : ℝ)^2093 ≤ (2669282057957/6250000000000 : ℝ)^1581 := by
    have hnat : (82171243 : ℕ)^2093*6250000000000^1581 ≤ 2669282057957^1581*156250000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82171243 156250000 2669282057957 6250000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074308389/5000000000 : ℝ), (5400179403/10000000000 : ℝ), (82171243/156250000 : ℝ)] ![(13058146489873/100000000000000 : ℝ), (11058335141281/25000000000000 : ℝ), (2669282057957/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074308389/5000000000 : ℝ)|^2093 ≤ (13058146489873/100000000000000 : ℝ)^1581
        have hw : |(-1074308389/5000000000 : ℝ)|=(1074308389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400179403/10000000000 : ℝ)|^2093 ≤ (11058335141281/25000000000000 : ℝ)^1581
        have hw : |(5400179403/10000000000 : ℝ)|=(5400179403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82171243/156250000 : ℝ)|^2093 ≤ (2669282057957/6250000000000 : ℝ)^1581
        have hw : |(82171243/156250000 : ℝ)|=(82171243/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s4_1 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4277263/8000000 : ℝ)*x 0 + (-444071341/2000000000 : ℝ)*x 1 + (5258960009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4277263/8000000 : ℝ)^2093 ≤ (21826522761667/50000000000000 : ℝ)^1581 := by
    have hnat : (4277263 : ℕ)^2093*50000000000000^1581 ≤ 21826522761667^1581*8000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4277263 8000000 21826522761667 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444071341/2000000000 : ℝ)^2093 ≤ (6819218310673/50000000000000 : ℝ)^1581 := by
    have hnat : (444071341 : ℕ)^2093*50000000000000^1581 ≤ 6819218310673^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444071341 2000000000 6819218310673 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258960009/10000000000 : ℝ)^2093 ≤ (21354258920277/50000000000000 : ℝ)^1581 := by
    have hnat : (5258960009 : ℕ)^2093*50000000000000^1581 ≤ 21354258920277^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258960009 10000000000 21354258920277 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4277263/8000000 : ℝ), (-444071341/2000000000 : ℝ), (5258960009/10000000000 : ℝ)] ![(21826522761667/50000000000000 : ℝ), (6819218310673/50000000000000 : ℝ), (21354258920277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4277263/8000000 : ℝ)|^2093 ≤ (21826522761667/50000000000000 : ℝ)^1581
        have hw : |(4277263/8000000 : ℝ)|=(4277263/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-444071341/2000000000 : ℝ)|^2093 ≤ (6819218310673/50000000000000 : ℝ)^1581
        have hw : |(-444071341/2000000000 : ℝ)|=(444071341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258960009/10000000000 : ℝ)|^2093 ≤ (21354258920277/50000000000000 : ℝ)^1581
        have hw : |(5258960009/10000000000 : ℝ)|=(5258960009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s4_2 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167080587/312500000 : ℝ)*x 0 + (1314740121/2500000000 : ℝ)*x 1 + (-34693063/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167080587/312500000 : ℝ)^2093 ≤ (2728315368177/6250000000000 : ℝ)^1581 := by
    have hnat : (167080587 : ℕ)^2093*6250000000000^1581 ≤ 2728315368177^1581*312500000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167080587 312500000 2728315368177 6250000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314740121/2500000000 : ℝ)^2093 ≤ (10677130736829/25000000000000 : ℝ)^1581 := by
    have hnat : (1314740121 : ℕ)^2093*25000000000000^1581 ≤ 10677130736829^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314740121 2500000000 10677130736829 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34693063/156250000 : ℝ)^2093 ≤ (681921557437/5000000000000 : ℝ)^1581 := by
    have hnat : (34693063 : ℕ)^2093*5000000000000^1581 ≤ 681921557437^1581*156250000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34693063 156250000 681921557437 5000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167080587/312500000 : ℝ), (1314740121/2500000000 : ℝ), (-34693063/156250000 : ℝ)] ![(2728315368177/6250000000000 : ℝ), (10677130736829/25000000000000 : ℝ), (681921557437/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167080587/312500000 : ℝ)|^2093 ≤ (2728315368177/6250000000000 : ℝ)^1581
        have hw : |(167080587/312500000 : ℝ)|=(167080587/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314740121/2500000000 : ℝ)|^2093 ≤ (10677130736829/25000000000000 : ℝ)^1581
        have hw : |(1314740121/2500000000 : ℝ)|=(1314740121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34693063/156250000 : ℝ)|^2093 ≤ (681921557437/5000000000000 : ℝ)^1581
        have hw : |(-34693063/156250000 : ℝ)|=(34693063/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s4_3 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (435907963/1000000000 : ℝ)*x 0 + (2109923493/5000000000 : ℝ)*x 1 + (1125709991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435907963/1000000000 : ℝ)^2093 ≤ (6662609619313/20000000000000 : ℝ)^1581 := by
    have hnat : (435907963 : ℕ)^2093*20000000000000^1581 ≤ 6662609619313^1581*1000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435907963 1000000000 6662609619313 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109923493/5000000000 : ℝ)^2093 ≤ (15955876593873/50000000000000 : ℝ)^1581 := by
    have hnat : (2109923493 : ℕ)^2093*50000000000000^1581 ≤ 15955876593873^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109923493 5000000000 15955876593873 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125709991/2500000000 : ℝ)^2093 ≤ (34775198698929/100000000000000 : ℝ)^1581 := by
    have hnat : (1125709991 : ℕ)^2093*100000000000000^1581 ≤ 34775198698929^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125709991 2500000000 34775198698929 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435907963/1000000000 : ℝ), (2109923493/5000000000 : ℝ), (1125709991/2500000000 : ℝ)] ![(6662609619313/20000000000000 : ℝ), (15955876593873/50000000000000 : ℝ), (34775198698929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435907963/1000000000 : ℝ)|^2093 ≤ (6662609619313/20000000000000 : ℝ)^1581
        have hw : |(435907963/1000000000 : ℝ)|=(435907963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2109923493/5000000000 : ℝ)|^2093 ≤ (15955876593873/50000000000000 : ℝ)^1581
        have hw : |(2109923493/5000000000 : ℝ)|=(2109923493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125709991/2500000000 : ℝ)|^2093 ≤ (34775198698929/100000000000000 : ℝ)^1581
        have hw : |(1125709991/2500000000 : ℝ)|=(1125709991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s4_4 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2148623571/10000000000 : ℝ)*x 0 + (5259357583/10000000000 : ℝ)*x 1 + (1349944931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148623571/10000000000 : ℝ)^2093 ≤ (261164022877/2000000000000 : ℝ)^1581 := by
    have hnat : (2148623571 : ℕ)^2093*2000000000000^1581 ≤ 261164022877^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148623571 10000000000 261164022877 2000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259357583/10000000000 : ℝ)^2093 ≤ (21356396120869/50000000000000 : ℝ)^1581 := by
    have hnat : (5259357583 : ℕ)^2093*50000000000000^1581 ≤ 21356396120869^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259357583 10000000000 21356396120869 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349944931/2500000000 : ℝ)^2093 ≤ (22114503301883/50000000000000 : ℝ)^1581 := by
    have hnat : (1349944931 : ℕ)^2093*50000000000000^1581 ≤ 22114503301883^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349944931 2500000000 22114503301883 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2148623571/10000000000 : ℝ), (5259357583/10000000000 : ℝ), (1349944931/2500000000 : ℝ)] ![(261164022877/2000000000000 : ℝ), (21356396120869/50000000000000 : ℝ), (22114503301883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2148623571/10000000000 : ℝ)|^2093 ≤ (261164022877/2000000000000 : ℝ)^1581
        have hw : |(-2148623571/10000000000 : ℝ)|=(2148623571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259357583/10000000000 : ℝ)|^2093 ≤ (21356396120869/50000000000000 : ℝ)^1581
        have hw : |(5259357583/10000000000 : ℝ)|=(5259357583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349944931/2500000000 : ℝ)|^2093 ≤ (22114503301883/50000000000000 : ℝ)^1581
        have hw : |(1349944931/2500000000 : ℝ)|=(1349944931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s4_5 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5310705907/10000000000 : ℝ)*x 0 + (-2079536347/10000000000 : ℝ)*x 1 + (2699889917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310705907/10000000000 : ℝ)^2093 ≤ (270410790021/625000000000 : ℝ)^1581 := by
    have hnat : (5310705907 : ℕ)^2093*625000000000^1581 ≤ 270410790021^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310705907 10000000000 270410790021 625000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079536347/10000000000 : ℝ)^2093 ≤ (1563158223343/12500000000000 : ℝ)^1581 := by
    have hnat : (2079536347 : ℕ)^2093*12500000000000^1581 ≤ 1563158223343^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079536347 10000000000 1563158223343 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699889917/5000000000 : ℝ)^2093 ≤ (11057251949137/25000000000000 : ℝ)^1581 := by
    have hnat : (2699889917 : ℕ)^2093*25000000000000^1581 ≤ 11057251949137^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699889917 5000000000 11057251949137 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310705907/10000000000 : ℝ), (-2079536347/10000000000 : ℝ), (2699889917/5000000000 : ℝ)] ![(270410790021/625000000000 : ℝ), (1563158223343/12500000000000 : ℝ), (11057251949137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310705907/10000000000 : ℝ)|^2093 ≤ (270410790021/625000000000 : ℝ)^1581
        have hw : |(5310705907/10000000000 : ℝ)|=(5310705907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079536347/10000000000 : ℝ)|^2093 ≤ (1563158223343/12500000000000 : ℝ)^1581
        have hw : |(-2079536347/10000000000 : ℝ)|=(2079536347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699889917/5000000000 : ℝ)|^2093 ≤ (11057251949137/25000000000000 : ℝ)^1581
        have hw : |(2699889917/5000000000 : ℝ)|=(2699889917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s4_6 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (165959561/312500000 : ℝ)*x 0 + (2699889831/5000000000 : ℝ)*x 1 + (-51988413/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165959561/312500000 : ℝ)^2093 ≤ (8653145377739/20000000000000 : ℝ)^1581 := by
    have hnat : (165959561 : ℕ)^2093*20000000000000^1581 ≤ 8653145377739^1581*312500000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165959561 312500000 8653145377739 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699889831/5000000000 : ℝ)^2093 ≤ (4422900593147/10000000000000 : ℝ)^1581 := by
    have hnat : (2699889831 : ℕ)^2093*10000000000000^1581 ≤ 4422900593147^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699889831 5000000000 4422900593147 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51988413/250000000 : ℝ)^2093 ≤ (2501053432797/20000000000000 : ℝ)^1581 := by
    have hnat : (51988413 : ℕ)^2093*20000000000000^1581 ≤ 2501053432797^1581*250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51988413 250000000 2501053432797 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165959561/312500000 : ℝ), (2699889831/5000000000 : ℝ), (-51988413/250000000 : ℝ)] ![(8653145377739/20000000000000 : ℝ), (4422900593147/10000000000000 : ℝ), (2501053432797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165959561/312500000 : ℝ)|^2093 ≤ (8653145377739/20000000000000 : ℝ)^1581
        have hw : |(165959561/312500000 : ℝ)|=(165959561/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699889831/5000000000 : ℝ)|^2093 ≤ (4422900593147/10000000000000 : ℝ)^1581
        have hw : |(2699889831/5000000000 : ℝ)|=(2699889831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51988413/250000000 : ℝ)|^2093 ≤ (2501053432797/20000000000000 : ℝ)^1581
        have hw : |(-51988413/250000000 : ℝ)|=(51988413/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s4_7 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2179546141/5000000000 : ℝ)*x 0 + (4502042811/10000000000 : ℝ)*x 1 + (52758103/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179546141/5000000000 : ℝ)^2093 ≤ (6662635219687/20000000000000 : ℝ)^1581 := by
    have hnat : (2179546141 : ℕ)^2093*20000000000000^1581 ≤ 6662635219687^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179546141 5000000000 6662635219687 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502042811/10000000000 : ℝ)^2093 ≤ (34767048847317/100000000000000 : ℝ)^1581 := by
    have hnat : (4502042811 : ℕ)^2093*100000000000000^1581 ≤ 34767048847317^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502042811 10000000000 34767048847317 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52758103/125000000 : ℝ)^2093 ≤ (7979943761029/25000000000000 : ℝ)^1581 := by
    have hnat : (52758103 : ℕ)^2093*25000000000000^1581 ≤ 7979943761029^1581*125000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52758103 125000000 7979943761029 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179546141/5000000000 : ℝ), (4502042811/10000000000 : ℝ), (52758103/125000000 : ℝ)] ![(6662635219687/20000000000000 : ℝ), (34767048847317/100000000000000 : ℝ), (7979943761029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179546141/5000000000 : ℝ)|^2093 ≤ (6662635219687/20000000000000 : ℝ)^1581
        have hw : |(2179546141/5000000000 : ℝ)|=(2179546141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502042811/10000000000 : ℝ)|^2093 ≤ (34767048847317/100000000000000 : ℝ)^1581
        have hw : |(4502042811/10000000000 : ℝ)|=(4502042811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52758103/125000000 : ℝ)|^2093 ≤ (7979943761029/25000000000000 : ℝ)^1581
        have hw : |(52758103/125000000 : ℝ)|=(52758103/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1179_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2811/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5371/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5371/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5371/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5371/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5371/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5371/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5371/50000 : ℝ) ^ (8371/2048 : ℝ) ≤ (10956079203875707/100000000000000000000 : ℝ) := by
    have hpowers : (5371/50000 : ℝ)^8371 ≤ (10956079203875707/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5371 : ℕ)^8371*100000000000000000000^2048 ≤ 10956079203875707^2048*50000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5371 50000 10956079203875707 100000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5371/50000 : ℝ)) (X := (10956079203875707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3691/25000 : ℝ) ^ (8371/2048 : ℝ) ≤ (20098916042039371/50000000000000000000 : ℝ) := by
    have hpowers : (3691/25000 : ℝ)^8371 ≤ (20098916042039371/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3691 : ℕ)^8371*50000000000000000000^2048 ≤ 20098916042039371^2048*25000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3691 25000 20098916042039371 50000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3691/25000 : ℝ)) (X := (20098916042039371/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010956079203875707/50000000000000000000 : ℝ) ≤ (500026802285937/500000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (50010956079203875707/50000000000000000000 : ℝ)^2048 ≤ (500026802285937/500000000000000 : ℝ)^8371 := by
      have hnat : (50010956079203875707 : ℕ)^2048*500000000000000^8371 ≤ 500026802285937^8371*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010956079203875707 50000000000000000000 500026802285937 500000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500026802285937/500000000000000 : ℝ)) (X := (50010956079203875707/50000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051153911287954449/100000000000000000000 : ℝ) ≤ (2000250252005019/2000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (100051153911287954449/100000000000000000000 : ℝ)^2048 ≤ (2000250252005019/2000000000000000 : ℝ)^8371 := by
      have hnat : (100051153911287954449 : ℕ)^2048*2000000000000000^8371 ≤ 2000250252005019^8371*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051153911287954449 100000000000000000000 2000250252005019 2000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000250252005019/2000000000000000 : ℝ)) (X := (100051153911287954449/100000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25020098916042039371/25000000000000000000 : ℝ) ≤ (200039329486629/200000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (25020098916042039371/25000000000000000000 : ℝ)^2048 ≤ (200039329486629/200000000000000 : ℝ)^8371 := by
      have hnat : (25020098916042039371 : ℕ)^2048*200000000000000^8371 ≤ 200039329486629^8371*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020098916042039371 25000000000000000000 200039329486629 200000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200039329486629/200000000000000 : ℝ)) (X := (25020098916042039371/25000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10956079203875707/100000000000000000000 : ℝ) ≤ ((2010339515586152073/2011000000000000000 : ℝ)+2*(143042861271/80440000000000 : ℝ)*(5371/50000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (2010339515586152073/2011000000000000000 : ℝ)+2*(143042861271/80440000000000 : ℝ)*(5371/50000 : ℝ)=(500026802285937/500000000000000 : ℝ) by norm_num, show 1+2*(10956079203875707/100000000000000000000 : ℝ)=(50010956079203875707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20098916042039371/50000000000000000000 : ℝ)+(10956079203875707/100000000000000000000 : ℝ) ≤ ((2010339515586152073/2011000000000000000 : ℝ)+(143042861271/80440000000000 : ℝ)*((3691/25000 : ℝ)+(5371/50000 : ℝ)))^(8371/2048 : ℝ) := by
    rw [show (2010339515586152073/2011000000000000000 : ℝ)+(143042861271/80440000000000 : ℝ)*((3691/25000 : ℝ)+(5371/50000 : ℝ))=(2000250252005019/2000000000000000 : ℝ) by norm_num, show 1+(20098916042039371/50000000000000000000 : ℝ)+(10956079203875707/100000000000000000000 : ℝ)=(100051153911287954449/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20098916042039371/50000000000000000000 : ℝ) ≤ ((2010339515586152073/2011000000000000000 : ℝ)+2*(143042861271/80440000000000 : ℝ)*(3691/25000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (2010339515586152073/2011000000000000000 : ℝ)+2*(143042861271/80440000000000 : ℝ)*(3691/25000 : ℝ)=(200039329486629/200000000000000 : ℝ) by norm_num, show 1+2*(20098916042039371/50000000000000000000 : ℝ)=(25020098916042039371/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2010339515586152073/2011000000000000000 : ℝ)*(X 1 0+X 2 0)+(143042861271/80440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (2010339515586152073/2011000000000000000 : ℝ)) (alpha := (143042861271/80440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2010339515586152073/2011000000000000000 : ℝ)*(X 0 1+X 2 1)+(143042861271/80440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (2010339515586152073/2011000000000000000 : ℝ)) (alpha := (143042861271/80440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2010339515586152073/2011000000000000000 : ℝ)*(X 0 2+X 1 2)+(143042861271/80440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (2010339515586152073/2011000000000000000 : ℝ)) (alpha := (143042861271/80440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1074308389/5000000000 : ℝ)*X 0 0+(5400179403/10000000000 : ℝ)*X 0 1+(82171243/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4277263/8000000 : ℝ)*X 1 0+(-444071341/2000000000 : ℝ)*X 1 1+(5258960009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167080587/312500000 : ℝ)*X 2 0+(1314740121/2500000000 : ℝ)*X 2 1+(-34693063/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435907963/1000000000 : ℝ)*X 0 0+(2109923493/5000000000 : ℝ)*X 0 1+(1125709991/2500000000 : ℝ)*X 0 2+(435907963/1000000000 : ℝ)*X 1 0+(2109923493/5000000000 : ℝ)*X 1 1+(1125709991/2500000000 : ℝ)*X 1 2+(435907963/1000000000 : ℝ)*X 2 0+(2109923493/5000000000 : ℝ)*X 2 1+(1125709991/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2148623571/10000000000 : ℝ)*X 0 0+(5259357583/10000000000 : ℝ)*X 0 1+(1349944931/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310705907/10000000000 : ℝ)*X 1 0+(-2079536347/10000000000 : ℝ)*X 1 1+(2699889917/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165959561/312500000 : ℝ)*X 2 0+(2699889831/5000000000 : ℝ)*X 2 1+(-51988413/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179546141/5000000000 : ℝ)*X 0 0+(4502042811/10000000000 : ℝ)*X 0 1+(52758103/125000000 : ℝ)*X 0 2+(2179546141/5000000000 : ℝ)*X 1 0+(4502042811/10000000000 : ℝ)*X 1 1+(52758103/125000000 : ℝ)*X 1 2+(2179546141/5000000000 : ℝ)*X 2 0+(4502042811/10000000000 : ℝ)*X 2 1+(52758103/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9308390457333791765092887/3142187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (850438043/100000000000000 : ℝ)*(base19) + (142130043/20000000000000 : ℝ)*(base23) + (67459417/50000000000000 : ℝ)*(lower2) + (524020939/100000000000000 : ℝ)*(upper5) + (82929281460649/1562500000000 : ℝ)*(major0) + (82929281460649/1562500000000 : ℝ)*(major1) + (82929281460649/1562500000000 : ℝ)*(major2) + (7081190761129473/100000000000000 : ℝ)*(sp0) + (1770310380813017/25000000000000 : ℝ)*(sp1) + (3540625863726909/50000000000000 : ℝ)*(sp2) + (883419970992779/25000000000000 : ℝ)*(sp3) + (61676974561/100000000000000 : ℝ)*(sp4) + (5032206961/50000000000000 : ℝ)*(sp5) + (15606141523/100000000000000 : ℝ)*(sp7) + (3533695490112639/100000000000000 : ℝ)*(f.failure) + (7081252438104033/100000000000000 : ℝ)*(f.sum) + (2194502575523/2011000000000000000000000000 : ℝ)*base66 + (36787381473502371/6284375000000000000000000000000 : ℝ)*base68 + (29139778406005873/3142187500000000000000000000000 : ℝ)*base70 + (20191953987843373/3142187500000000000000000000000 : ℝ)*base72 + (13598363559077/2011000000000000000000000000 : ℝ)*base74 + (59503466713837877/3142187500000000000000000000000 : ℝ)*base75 + (2856337295368063/785546875000000000000000000000 : ℝ)*base77 + (35484236065783621/6284375000000000000000000000000 : ℝ)*base80 + (10319249529/6284375000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1168813/5000000000000000000000 : ℝ)*base89 + (1168813/5000000000000000000000 : ℝ)*base91 + (1168813/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7847120946718252900691829/10055000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (820437067/100000000000000 : ℝ)*(base19) + (79428161/6250000000000 : ℝ)*(base23) + (6919629/3125000000000 : ℝ)*(upper2) + (157853839/100000000000000 : ℝ)*(upper5) + (1067511261308691/20000000000000 : ℝ)*(major0) + (1067511261308691/20000000000000 : ℝ)*(major1) + (1067511261308691/20000000000000 : ℝ)*(major2) + (777989667/50000000000000 : ℝ)*(sp0) + (4240043201/12500000000000 : ℝ)*(sp1) + (7485394569/25000000000000 : ℝ)*(sp2) + (7121386867631783/100000000000000 : ℝ)*(sp4) + (3560676841414221/50000000000000 : ℝ)*(sp5) + (890169651397783/12500000000000 : ℝ)*(sp6) + (1776862081730897/50000000000000 : ℝ)*(sp7) + (1776862081730897/50000000000000 : ℝ)*(f.failure) + (7121388423611117/100000000000000 : ℝ)*(f.sum) + (3662531058119/4022000000000000000000000000 : ℝ)*base65 + (356523047746408557/40220000000000000000000000000000 : ℝ)*base68 + (104907845661308557/40220000000000000000000000000000 : ℝ)*base70 + (272379983377348557/40220000000000000000000000000000 : ℝ)*base72 + (2111312401387/804400000000000000000000000 : ℝ)*base74 + (592726687086108557/40220000000000000000000000000000 : ℝ)*base76 + (188826987042691443/40220000000000000000000000000000 : ℝ)*base77 + (117851223483828557/40220000000000000000000000000000 : ℝ)*base80 + (22887694370551/4022000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3876099/2500000000000000000000 : ℝ)*base89 + (3876099/2500000000000000000000 : ℝ)*base91 + (3876099/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1179_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1179_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1179_s5_0 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-537294757/2500000000 : ℝ)*x 0 + (2696978823/5000000000 : ℝ)*x 1 + (210592477/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537294757/2500000000 : ℝ)^2093 ≤ (13062670335709/100000000000000 : ℝ)^1581 := by
    have hnat : (537294757 : ℕ)^2093*100000000000000^1581 ≤ 13062670335709^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537294757 2500000000 13062670335709 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696978823/5000000000 : ℝ)^2093 ≤ (345045984911/781250000000 : ℝ)^1581 := by
    have hnat : (2696978823 : ℕ)^2093*781250000000^1581 ≤ 345045984911^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696978823 5000000000 345045984911 781250000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210592477/400000000 : ℝ)^2093 ≤ (42771443575699/100000000000000 : ℝ)^1581 := by
    have hnat : (210592477 : ℕ)^2093*100000000000000^1581 ≤ 42771443575699^1581*400000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210592477 400000000 42771443575699 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537294757/2500000000 : ℝ), (2696978823/5000000000 : ℝ), (210592477/400000000 : ℝ)] ![(13062670335709/100000000000000 : ℝ), (345045984911/781250000000 : ℝ), (42771443575699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537294757/2500000000 : ℝ)|^2093 ≤ (13062670335709/100000000000000 : ℝ)^1581
        have hw : |(-537294757/2500000000 : ℝ)|=(537294757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696978823/5000000000 : ℝ)|^2093 ≤ (345045984911/781250000000 : ℝ)^1581
        have hw : |(2696978823/5000000000 : ℝ)|=(2696978823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210592477/400000000 : ℝ)|^2093 ≤ (42771443575699/100000000000000 : ℝ)^1581
        have hw : |(210592477/400000000 : ℝ)|=(210592477/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s5_1 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345012887/10000000000 : ℝ)*x 0 + (-553674321/2500000000 : ℝ)*x 1 + (1316202981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345012887/10000000000 : ℝ)^2093 ≤ (10909030321531/25000000000000 : ℝ)^1581 := by
    have hnat : (5345012887 : ℕ)^2093*25000000000000^1581 ≤ 10909030321531^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345012887 10000000000 10909030321531 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553674321/2500000000 : ℝ)^2093 ≤ (6796217570009/50000000000000 : ℝ)^1581 := by
    have hnat : (553674321 : ℕ)^2093*50000000000000^1581 ≤ 6796217570009^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553674321 2500000000 6796217570009 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316202981/2500000000 : ℝ)^2093 ≤ (2673215222809/6250000000000 : ℝ)^1581 := by
    have hnat : (1316202981 : ℕ)^2093*6250000000000^1581 ≤ 2673215222809^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316202981 2500000000 2673215222809 6250000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345012887/10000000000 : ℝ), (-553674321/2500000000 : ℝ), (1316202981/2500000000 : ℝ)] ![(10909030321531/25000000000000 : ℝ), (6796217570009/50000000000000 : ℝ), (2673215222809/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345012887/10000000000 : ℝ)|^2093 ≤ (10909030321531/25000000000000 : ℝ)^1581
        have hw : |(5345012887/10000000000 : ℝ)|=(5345012887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553674321/2500000000 : ℝ)|^2093 ≤ (6796217570009/50000000000000 : ℝ)^1581
        have hw : |(-553674321/2500000000 : ℝ)|=(553674321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316202981/2500000000 : ℝ)|^2093 ≤ (2673215222809/6250000000000 : ℝ)^1581
        have hw : |(1316202981/2500000000 : ℝ)|=(1316202981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s5_2 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668126611/1250000000 : ℝ)*x 0 + (5264811921/10000000000 : ℝ)*x 1 + (-1107348643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668126611/1250000000 : ℝ)^2093 ≤ (43636121296931/100000000000000 : ℝ)^1581 := by
    have hnat : (668126611 : ℕ)^2093*100000000000000^1581 ≤ 43636121296931^1581*1250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668126611 1250000000 43636121296931 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264811921/10000000000 : ℝ)^2093 ≤ (42771443532679/100000000000000 : ℝ)^1581 := by
    have hnat : (5264811921 : ℕ)^2093*100000000000000^1581 ≤ 42771443532679^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264811921 10000000000 42771443532679 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107348643/5000000000 : ℝ)^2093 ≤ (3398108789067/25000000000000 : ℝ)^1581 := by
    have hnat : (1107348643 : ℕ)^2093*25000000000000^1581 ≤ 3398108789067^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107348643 5000000000 3398108789067 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668126611/1250000000 : ℝ), (5264811921/10000000000 : ℝ), (-1107348643/5000000000 : ℝ)] ![(43636121296931/100000000000000 : ℝ), (42771443532679/100000000000000 : ℝ), (3398108789067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668126611/1250000000 : ℝ)|^2093 ≤ (43636121296931/100000000000000 : ℝ)^1581
        have hw : |(668126611/1250000000 : ℝ)|=(668126611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264811921/10000000000 : ℝ)|^2093 ≤ (42771443532679/100000000000000 : ℝ)^1581
        have hw : |(5264811921/10000000000 : ℝ)|=(5264811921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1107348643/5000000000 : ℝ)|^2093 ≤ (3398108789067/25000000000000 : ℝ)^1581
        have hw : |(-1107348643/5000000000 : ℝ)|=(1107348643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s5_3 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4359407007/10000000000 : ℝ)*x 0 + (528987809/1250000000 : ℝ)*x 1 + (280668783/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359407007/10000000000 : ℝ)^2093 ≤ (33316360249437/100000000000000 : ℝ)^1581 := by
    have hnat : (4359407007 : ℕ)^2093*100000000000000^1581 ≤ 33316360249437^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359407007 10000000000 33316360249437 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528987809/1250000000 : ℝ)^2093 ≤ (6406500060771/20000000000000 : ℝ)^1581 := by
    have hnat : (528987809 : ℕ)^2093*20000000000000^1581 ≤ 6406500060771^1581*1250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528987809 1250000000 6406500060771 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280668783/625000000 : ℝ)^2093 ≤ (34651139425167/100000000000000 : ℝ)^1581 := by
    have hnat : (280668783 : ℕ)^2093*100000000000000^1581 ≤ 34651139425167^1581*625000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280668783 625000000 34651139425167 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359407007/10000000000 : ℝ), (528987809/1250000000 : ℝ), (280668783/625000000 : ℝ)] ![(33316360249437/100000000000000 : ℝ), (6406500060771/20000000000000 : ℝ), (34651139425167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359407007/10000000000 : ℝ)|^2093 ≤ (33316360249437/100000000000000 : ℝ)^1581
        have hw : |(4359407007/10000000000 : ℝ)|=(4359407007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528987809/1250000000 : ℝ)|^2093 ≤ (6406500060771/20000000000000 : ℝ)^1581
        have hw : |(528987809/1250000000 : ℝ)|=(528987809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280668783/625000000 : ℝ)|^2093 ≤ (34651139425167/100000000000000 : ℝ)^1581
        have hw : |(280668783/625000000 : ℝ)|=(280668783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s5_4 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074592091/5000000000 : ℝ)*x 0 + (2632572381/5000000000 : ℝ)*x 1 + (5393623579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074592091/5000000000 : ℝ)^2093 ≤ (3265677951601/25000000000000 : ℝ)^1581 := by
    have hnat : (1074592091 : ℕ)^2093*25000000000000^1581 ≤ 3265677951601^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074592091 5000000000 3265677951601 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632572381/5000000000 : ℝ)^2093 ≤ (21387511628857/50000000000000 : ℝ)^1581 := by
    have hnat : (2632572381 : ℕ)^2093*50000000000000^1581 ≤ 21387511628857^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632572381 5000000000 21387511628857 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393623579/10000000000 : ℝ)^2093 ≤ (44162264922937/100000000000000 : ℝ)^1581 := by
    have hnat : (5393623579 : ℕ)^2093*100000000000000^1581 ≤ 44162264922937^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393623579 10000000000 44162264922937 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074592091/5000000000 : ℝ), (2632572381/5000000000 : ℝ), (5393623579/10000000000 : ℝ)] ![(3265677951601/25000000000000 : ℝ), (21387511628857/50000000000000 : ℝ), (44162264922937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074592091/5000000000 : ℝ)|^2093 ≤ (3265677951601/25000000000000 : ℝ)^1581
        have hw : |(-1074592091/5000000000 : ℝ)|=(1074592091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632572381/5000000000 : ℝ)|^2093 ≤ (21387511628857/50000000000000 : ℝ)^1581
        have hw : |(2632572381/5000000000 : ℝ)|=(2632572381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393623579/10000000000 : ℝ)|^2093 ≤ (44162264922937/100000000000000 : ℝ)^1581
        have hw : |(5393623579/10000000000 : ℝ)|=(5393623579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s5_5 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312205191/10000000000 : ℝ)*x 0 + (-208588571/1000000000 : ℝ)*x 1 + (5393623599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312205191/10000000000 : ℝ)^2093 ≤ (10820474313479/25000000000000 : ℝ)^1581 := by
    have hnat : (5312205191 : ℕ)^2093*25000000000000^1581 ≤ 10820474313479^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312205191 10000000000 10820474313479 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208588571/1000000000 : ℝ)^2093 ≤ (1569479698721/12500000000000 : ℝ)^1581 := by
    have hnat : (208588571 : ℕ)^2093*12500000000000^1581 ≤ 1569479698721^1581*1000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208588571 1000000000 1569479698721 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393623599/10000000000 : ℝ)^2093 ≤ (44162265139727/100000000000000 : ℝ)^1581 := by
    have hnat : (5393623599 : ℕ)^2093*100000000000000^1581 ≤ 44162265139727^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393623599 10000000000 44162265139727 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312205191/10000000000 : ℝ), (-208588571/1000000000 : ℝ), (5393623599/10000000000 : ℝ)] ![(10820474313479/25000000000000 : ℝ), (1569479698721/12500000000000 : ℝ), (44162265139727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312205191/10000000000 : ℝ)|^2093 ≤ (10820474313479/25000000000000 : ℝ)^1581
        have hw : |(5312205191/10000000000 : ℝ)|=(5312205191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-208588571/1000000000 : ℝ)|^2093 ≤ (1569479698721/12500000000000 : ℝ)^1581
        have hw : |(-208588571/1000000000 : ℝ)|=(208588571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393623599/10000000000 : ℝ)|^2093 ≤ (44162265139727/100000000000000 : ℝ)^1581
        have hw : |(5393623599/10000000000 : ℝ)|=(5393623599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s5_6 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312205293/10000000000 : ℝ)*x 0 + (674202939/1250000000 : ℝ)*x 1 + (-2085885691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312205293/10000000000 : ℝ)^2093 ≤ (43281898354109/100000000000000 : ℝ)^1581 := by
    have hnat : (5312205293 : ℕ)^2093*100000000000000^1581 ≤ 43281898354109^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312205293 10000000000 43281898354109 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674202939/1250000000 : ℝ)^2093 ≤ (44162264196693/100000000000000 : ℝ)^1581 := by
    have hnat : (674202939 : ℕ)^2093*100000000000000^1581 ≤ 44162264196693^1581*1250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674202939 1250000000 44162264196693 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085885691/10000000000 : ℝ)^2093 ≤ (12555837438361/100000000000000 : ℝ)^1581 := by
    have hnat : (2085885691 : ℕ)^2093*100000000000000^1581 ≤ 12555837438361^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085885691 10000000000 12555837438361 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312205293/10000000000 : ℝ), (674202939/1250000000 : ℝ), (-2085885691/10000000000 : ℝ)] ![(43281898354109/100000000000000 : ℝ), (44162264196693/100000000000000 : ℝ), (12555837438361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312205293/10000000000 : ℝ)|^2093 ≤ (43281898354109/100000000000000 : ℝ)^1581
        have hw : |(5312205293/10000000000 : ℝ)|=(5312205293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674202939/1250000000 : ℝ)|^2093 ≤ (44162264196693/100000000000000 : ℝ)^1581
        have hw : |(674202939/1250000000 : ℝ)|=(674202939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2085885691/10000000000 : ℝ)|^2093 ≤ (12555837438361/100000000000000 : ℝ)^1581
        have hw : |(-2085885691/10000000000 : ℝ)|=(2085885691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s5_7 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4359417351/10000000000 : ℝ)*x 0 + (2245016767/5000000000 : ℝ)*x 1 + (846514387/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359417351/10000000000 : ℝ)^2093 ≤ (33316464903519/100000000000000 : ℝ)^1581 := by
    have hnat : (4359417351 : ℕ)^2093*100000000000000^1581 ≤ 33316464903519^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359417351 10000000000 33316464903519 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245016767/5000000000 : ℝ)^2093 ≤ (4330540775933/12500000000000 : ℝ)^1581 := by
    have hnat : (2245016767 : ℕ)^2093*12500000000000^1581 ≤ 4330540775933^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245016767 5000000000 4330540775933 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846514387/2000000000 : ℝ)^2093 ≤ (6407841775681/20000000000000 : ℝ)^1581 := by
    have hnat : (846514387 : ℕ)^2093*20000000000000^1581 ≤ 6407841775681^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846514387 2000000000 6407841775681 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359417351/10000000000 : ℝ), (2245016767/5000000000 : ℝ), (846514387/2000000000 : ℝ)] ![(33316464903519/100000000000000 : ℝ), (4330540775933/12500000000000 : ℝ), (6407841775681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359417351/10000000000 : ℝ)|^2093 ≤ (33316464903519/100000000000000 : ℝ)^1581
        have hw : |(4359417351/10000000000 : ℝ)|=(4359417351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245016767/5000000000 : ℝ)|^2093 ≤ (4330540775933/12500000000000 : ℝ)^1581
        have hw : |(2245016767/5000000000 : ℝ)|=(2245016767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846514387/2000000000 : ℝ)|^2093 ≤ (6407841775681/20000000000000 : ℝ)^1581
        have hw : |(846514387/2000000000 : ℝ)|=(846514387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1179_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1421/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1763/12500 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2811/25000 : ℝ) ^ (8371/2048 : ℝ) ≤ (3301198302785109/25000000000000000000 : ℝ) := by
    have hpowers : (2811/25000 : ℝ)^8371 ≤ (3301198302785109/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2811 : ℕ)^8371*25000000000000000000^2048 ≤ 3301198302785109^2048*25000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 25000 3301198302785109 25000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/25000 : ℝ)) (X := (3301198302785109/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8371/2048 : ℝ) ≤ (17309185903462669/50000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8371 ≤ (17309185903462669/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8371*50000000000000000000^2048 ≤ 17309185903462669^2048*50000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 17309185903462669 50000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (17309185903462669/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503301198302785109/12500000000000000000 : ℝ) ≤ (10000646057091211/10000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (12503301198302785109/12500000000000000000 : ℝ)^2048 ≤ (10000646057091211/10000000000000000 : ℝ)^8371 := by
      have hnat : (12503301198302785109 : ℕ)^2048*10000000000000000^8371 ≤ 10000646057091211^8371*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503301198302785109 12500000000000000000 10000646057091211 10000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000646057091211/10000000000000000 : ℝ)) (X := (12503301198302785109/12500000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023911582509032887/50000000000000000000 : ℝ) ≤ (2000233960475751/2000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (50023911582509032887/50000000000000000000 : ℝ)^2048 ≤ (2000233960475751/2000000000000000 : ℝ)^8371 := by
      have hnat : (50023911582509032887 : ℕ)^2048*2000000000000000^8371 ≤ 2000233960475751^8371*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023911582509032887 50000000000000000000 2000233960475751 2000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000233960475751/2000000000000000 : ℝ)) (X := (50023911582509032887/50000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017309185903462669/25000000000000000000 : ℝ) ≤ (10001693547666299/10000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (25017309185903462669/25000000000000000000 : ℝ)^2048 ≤ (10001693547666299/10000000000000000 : ℝ)^8371 := by
      have hnat : (25017309185903462669 : ℕ)^2048*10000000000000000^8371 ≤ 10001693547666299^8371*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017309185903462669 25000000000000000000 10001693547666299 10000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001693547666299/10000000000000000 : ℝ)) (X := (25017309185903462669/25000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3301198302785109/25000000000000000000 : ℝ) ≤ ((14945076863338215709/14950000000000000000 : ℝ)+2*(65468160943/37375000000000 : ℝ)*(2811/25000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (14945076863338215709/14950000000000000000 : ℝ)+2*(65468160943/37375000000000 : ℝ)*(2811/25000 : ℝ)=(10000646057091211/10000000000000000 : ℝ) by norm_num, show 1+2*(3301198302785109/25000000000000000000 : ℝ)=(12503301198302785109/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17309185903462669/50000000000000000000 : ℝ)+(3301198302785109/25000000000000000000 : ℝ) ≤ ((14945076863338215709/14950000000000000000 : ℝ)+(65468160943/37375000000000 : ℝ)*((7117/50000 : ℝ)+(2811/25000 : ℝ)))^(8371/2048 : ℝ) := by
    rw [show (14945076863338215709/14950000000000000000 : ℝ)+(65468160943/37375000000000 : ℝ)*((7117/50000 : ℝ)+(2811/25000 : ℝ))=(2000233960475751/2000000000000000 : ℝ) by norm_num, show 1+(17309185903462669/50000000000000000000 : ℝ)+(3301198302785109/25000000000000000000 : ℝ)=(50023911582509032887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17309185903462669/50000000000000000000 : ℝ) ≤ ((14945076863338215709/14950000000000000000 : ℝ)+2*(65468160943/37375000000000 : ℝ)*(7117/50000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (14945076863338215709/14950000000000000000 : ℝ)+2*(65468160943/37375000000000 : ℝ)*(7117/50000 : ℝ)=(10001693547666299/10000000000000000 : ℝ) by norm_num, show 1+2*(17309185903462669/50000000000000000000 : ℝ)=(25017309185903462669/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14945076863338215709/14950000000000000000 : ℝ)*(X 1 0+X 2 0)+(65468160943/37375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14945076863338215709/14950000000000000000 : ℝ)) (alpha := (65468160943/37375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14945076863338215709/14950000000000000000 : ℝ)*(X 0 1+X 2 1)+(65468160943/37375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14945076863338215709/14950000000000000000 : ℝ)) (alpha := (65468160943/37375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14945076863338215709/14950000000000000000 : ℝ)*(X 0 2+X 1 2)+(65468160943/37375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14945076863338215709/14950000000000000000 : ℝ)) (alpha := (65468160943/37375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-537294757/2500000000 : ℝ)*X 0 0+(2696978823/5000000000 : ℝ)*X 0 1+(210592477/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345012887/10000000000 : ℝ)*X 1 0+(-553674321/2500000000 : ℝ)*X 1 1+(1316202981/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668126611/1250000000 : ℝ)*X 2 0+(5264811921/10000000000 : ℝ)*X 2 1+(-1107348643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359407007/10000000000 : ℝ)*X 0 0+(528987809/1250000000 : ℝ)*X 0 1+(280668783/625000000 : ℝ)*X 0 2+(4359407007/10000000000 : ℝ)*X 1 0+(528987809/1250000000 : ℝ)*X 1 1+(280668783/625000000 : ℝ)*X 1 2+(4359407007/10000000000 : ℝ)*X 2 0+(528987809/1250000000 : ℝ)*X 2 1+(280668783/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1074592091/5000000000 : ℝ)*X 0 0+(2632572381/5000000000 : ℝ)*X 0 1+(5393623579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312205191/10000000000 : ℝ)*X 1 0+(-208588571/1000000000 : ℝ)*X 1 1+(5393623599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312205293/10000000000 : ℝ)*X 2 0+(674202939/1250000000 : ℝ)*X 2 1+(-2085885691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359417351/10000000000 : ℝ)*X 0 0+(2245016767/5000000000 : ℝ)*X 0 1+(846514387/2000000000 : ℝ)*X 0 2+(4359417351/10000000000 : ℝ)*X 1 0+(2245016767/5000000000 : ℝ)*X 1 1+(846514387/2000000000 : ℝ)*X 1 2+(4359417351/10000000000 : ℝ)*X 2 0+(2245016767/5000000000 : ℝ)*X 2 1+(846514387/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (594053783787294006170228163/57500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2022502443/100000000000000 : ℝ)*(base19) + (941606161/50000000000000 : ℝ)*(base23) + (75225077/100000000000000 : ℝ)*(lower2) + (131456933/50000000000000 : ℝ)*(upper3) + (155390629/100000000000000 : ℝ)*(upper5) + (5803687104972497/100000000000000 : ℝ)*(major0) + (5803687104972497/100000000000000 : ℝ)*(major1) + (5803687104972497/100000000000000 : ℝ)*(major2) + (3871623878860889/50000000000000 : ℝ)*(sp0) + (7743299612700739/100000000000000 : ℝ)*(sp1) + (387164987599543/5000000000000 : ℝ)*(sp2) + (966010729533177/25000000000000 : ℝ)*(sp3) + (13469370351/25000000000000 : ℝ)*(sp4) + (2931223009/10000000000000 : ℝ)*(sp7) + (1932036115181399/50000000000000 : ℝ)*(f.failure) + (7743301635203181/100000000000000 : ℝ)*(f.sum) + (459646650559/287500000000000000000000000 : ℝ)*base65 + (525002748517442721/115000000000000000000000000000000 : ℝ)*base67 + (982452771302557279/115000000000000000000000000000000 : ℝ)*base70 + (1728306701312442721/115000000000000000000000000000000 : ℝ)*base71 + (749983305333/143750000000000000000000000 : ℝ)*base74 + (653067962352557279/115000000000000000000000000000000 : ℝ)*base76 + (747503020192557279/115000000000000000000000000000000 : ℝ)*base78 + (533482738242557279/115000000000000000000000000000000 : ℝ)*base80 + (1667403348691/287500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5744267/2500000000000000000000 : ℝ)*base90 + (5744267/2500000000000000000000 : ℝ)*base92 + (5744267/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11491835498452964507616753/1625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1034867611/100000000000000 : ℝ)*(base19) + (165482343/12500000000000 : ℝ)*(base23) + (27505049/20000000000000 : ℝ)*(upper3) + (2320333/4000000000000 : ℝ)*(lower4) + (14612109/10000000000000 : ℝ)*(upper5) + (583372974317903/10000000000000 : ℝ)*(major0) + (583372974317903/10000000000000 : ℝ)*(major1) + (583372974317903/10000000000000 : ℝ)*(major2) + (27539467993/100000000000000 : ℝ)*(sp1) + (32452800467/100000000000000 : ℝ)*(sp2) + (3891692374482067/50000000000000 : ℝ)*(sp4) + (778335617462853/10000000000000 : ℝ)*(sp5) + (7783350972304923/100000000000000 : ℝ)*(sp6) + (1942037250831979/50000000000000 : ℝ)*(sp7) + (1942037250831979/50000000000000 : ℝ)*(f.failure) + (3891692374482067/50000000000000 : ℝ)*(f.sum) + (1241191914791/747500000000000000000000000 : ℝ)*base65 + (3022249777206138227/149500000000000000000000000000000 : ℝ)*base67 + (1829030382124138227/149500000000000000000000000000000 : ℝ)*base69 + (240633850655638227/149500000000000000000000000000000 : ℝ)*base71 + (1056603965383/373750000000000000000000000 : ℝ)*base73 + (3972604375932138227/149500000000000000000000000000000 : ℝ)*base75 + (193850690887361773/149500000000000000000000000000000 : ℝ)*base78 + (1980810266243638227/149500000000000000000000000000000 : ℝ)*base79 + (7525777815393/1495000000000000000000000000 : ℝ)*base82 + (14684593/2500000000000000000000 : ℝ)*base89 + (14684593/2500000000000000000000 : ℝ)*base91 + (14684593/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1179_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1179_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1179_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3279/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1179_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1179_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1179_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3279/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1179_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
