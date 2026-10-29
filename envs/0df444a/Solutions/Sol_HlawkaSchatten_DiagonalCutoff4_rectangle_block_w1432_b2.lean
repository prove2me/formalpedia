-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1432_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:04.179005+00:00
-- url     : https://prove2.me/submissions/c7dd1943-edaf-44c4-8ca4-b4458d644122

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
theorem support_rectangle_w1432_s6_0 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-984348921/5000000000 : ℝ)*x 0 + (676008199/1250000000 : ℝ)*x 1 + (327935789/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (984348921/5000000000 : ℝ)^549 ≤ (3002774265447/25000000000000 : ℝ)^421 := by
    have hnat : (984348921 : ℕ)^549*25000000000000^421 ≤ 3002774265447^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984348921 5000000000 3002774265447 25000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676008199/1250000000 : ℝ)^549 ≤ (358894286507/800000000000 : ℝ)^421 := by
    have hnat : (676008199 : ℕ)^549*800000000000^421 ≤ 358894286507^421*1250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676008199 1250000000 358894286507 800000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327935789/625000000 : ℝ)^549 ≤ (21563558557041/50000000000000 : ℝ)^421 := by
    have hnat : (327935789 : ℕ)^549*50000000000000^421 ≤ 21563558557041^421*625000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327935789 625000000 21563558557041 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-984348921/5000000000 : ℝ), (676008199/1250000000 : ℝ), (327935789/625000000 : ℝ)] ![(3002774265447/25000000000000 : ℝ), (358894286507/800000000000 : ℝ), (21563558557041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-984348921/5000000000 : ℝ)|^549 ≤ (3002774265447/25000000000000 : ℝ)^421
        have hw : |(-984348921/5000000000 : ℝ)|=(984348921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676008199/1250000000 : ℝ)|^549 ≤ (358894286507/800000000000 : ℝ)^421
        have hw : |(676008199/1250000000 : ℝ)|=(676008199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327935789/625000000 : ℝ)|^549 ≤ (21563558557041/50000000000000 : ℝ)^421
        have hw : |(327935789/625000000 : ℝ)|=(327935789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s6_1 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1336816111/2500000000 : ℝ)*x 0 + (-1025355377/5000000000 : ℝ)*x 1 + (327935789/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336816111/2500000000 : ℝ)^549 ≤ (8841039908167/20000000000000 : ℝ)^421 := by
    have hnat : (1336816111 : ℕ)^549*20000000000000^421 ≤ 8841039908167^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336816111 2500000000 8841039908167 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025355377/5000000000 : ℝ)^549 ≤ (1583460416429/12500000000000 : ℝ)^421 := by
    have hnat : (1025355377 : ℕ)^549*12500000000000^421 ≤ 1583460416429^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025355377 5000000000 1583460416429 12500000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327935789/625000000 : ℝ)^549 ≤ (21563558557041/50000000000000 : ℝ)^421 := by
    have hnat : (327935789 : ℕ)^549*50000000000000^421 ≤ 21563558557041^421*625000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327935789 625000000 21563558557041 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336816111/2500000000 : ℝ), (-1025355377/5000000000 : ℝ), (327935789/625000000 : ℝ)] ![(8841039908167/20000000000000 : ℝ), (1583460416429/12500000000000 : ℝ), (21563558557041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336816111/2500000000 : ℝ)|^549 ≤ (8841039908167/20000000000000 : ℝ)^421
        have hw : |(1336816111/2500000000 : ℝ)|=(1336816111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025355377/5000000000 : ℝ)|^549 ≤ (1583460416429/12500000000000 : ℝ)^421
        have hw : |(-1025355377/5000000000 : ℝ)|=(1025355377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327935789/625000000 : ℝ)|^549 ≤ (21563558557041/50000000000000 : ℝ)^421
        have hw : |(327935789/625000000 : ℝ)|=(327935789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s6_2 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1336816111/2500000000 : ℝ)*x 0 + (327935789/625000000 : ℝ)*x 1 + (-1025355377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336816111/2500000000 : ℝ)^549 ≤ (8841039908167/20000000000000 : ℝ)^421 := by
    have hnat : (1336816111 : ℕ)^549*20000000000000^421 ≤ 8841039908167^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336816111 2500000000 8841039908167 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327935789/625000000 : ℝ)^549 ≤ (21563558557041/50000000000000 : ℝ)^421 := by
    have hnat : (327935789 : ℕ)^549*50000000000000^421 ≤ 21563558557041^421*625000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327935789 625000000 21563558557041 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025355377/5000000000 : ℝ)^549 ≤ (1583460416429/12500000000000 : ℝ)^421 := by
    have hnat : (1025355377 : ℕ)^549*12500000000000^421 ≤ 1583460416429^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025355377 5000000000 1583460416429 12500000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336816111/2500000000 : ℝ), (327935789/625000000 : ℝ), (-1025355377/5000000000 : ℝ)] ![(8841039908167/20000000000000 : ℝ), (21563558557041/50000000000000 : ℝ), (1583460416429/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336816111/2500000000 : ℝ)|^549 ≤ (8841039908167/20000000000000 : ℝ)^421
        have hw : |(1336816111/2500000000 : ℝ)|=(1336816111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327935789/625000000 : ℝ)|^549 ≤ (21563558557041/50000000000000 : ℝ)^421
        have hw : |(327935789/625000000 : ℝ)|=(327935789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025355377/5000000000 : ℝ)|^549 ≤ (1583460416429/12500000000000 : ℝ)^421
        have hw : |(-1025355377/5000000000 : ℝ)|=(1025355377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s6_3 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4303623627/10000000000 : ℝ)*x 0 + (4132358959/10000000000 : ℝ)*x 1 + (2240620009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303623627/10000000000 : ℝ)^549 ≤ (33304735519307/100000000000000 : ℝ)^421 := by
    have hnat : (4303623627 : ℕ)^549*100000000000000^421 ≤ 33304735519307^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303623627 10000000000 33304735519307 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4132358959/10000000000 : ℝ)^549 ≤ (31586947414833/100000000000000 : ℝ)^421 := by
    have hnat : (4132358959 : ℕ)^549*100000000000000^421 ≤ 31586947414833^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132358959 10000000000 31586947414833 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240620009/5000000000 : ℝ)^549 ≤ (17554158522969/50000000000000 : ℝ)^421 := by
    have hnat : (2240620009 : ℕ)^549*50000000000000^421 ≤ 17554158522969^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240620009 5000000000 17554158522969 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303623627/10000000000 : ℝ), (4132358959/10000000000 : ℝ), (2240620009/5000000000 : ℝ)] ![(33304735519307/100000000000000 : ℝ), (31586947414833/100000000000000 : ℝ), (17554158522969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303623627/10000000000 : ℝ)|^549 ≤ (33304735519307/100000000000000 : ℝ)^421
        have hw : |(4303623627/10000000000 : ℝ)|=(4303623627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4132358959/10000000000 : ℝ)|^549 ≤ (31586947414833/100000000000000 : ℝ)^421
        have hw : |(4132358959/10000000000 : ℝ)|=(4132358959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240620009/5000000000 : ℝ)|^549 ≤ (17554158522969/50000000000000 : ℝ)^421
        have hw : |(2240620009/5000000000 : ℝ)|=(2240620009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s6_4 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-492177291/2500000000 : ℝ)*x 0 + (2623776899/5000000000 : ℝ)*x 1 + (540748139/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (492177291/2500000000 : ℝ)^549 ≤ (12011187139509/100000000000000 : ℝ)^421 := by
    have hnat : (492177291 : ℕ)^549*100000000000000^421 ≤ 12011187139509^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492177291 2500000000 12011187139509 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623776899/5000000000 : ℝ)^549 ≤ (21566673250941/50000000000000 : ℝ)^421 := by
    have hnat : (2623776899 : ℕ)^549*50000000000000^421 ≤ 21566673250941^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623776899 5000000000 21566673250941 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540748139/1000000000 : ℝ)^549 ≤ (22427733170911/50000000000000 : ℝ)^421 := by
    have hnat : (540748139 : ℕ)^549*50000000000000^421 ≤ 22427733170911^421*1000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540748139 1000000000 22427733170911 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-492177291/2500000000 : ℝ), (2623776899/5000000000 : ℝ), (540748139/1000000000 : ℝ)] ![(12011187139509/100000000000000 : ℝ), (21566673250941/50000000000000 : ℝ), (22427733170911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-492177291/2500000000 : ℝ)|^549 ≤ (12011187139509/100000000000000 : ℝ)^421
        have hw : |(-492177291/2500000000 : ℝ)|=(492177291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623776899/5000000000 : ℝ)|^549 ≤ (21566673250941/50000000000000 : ℝ)^421
        have hw : |(2623776899/5000000000 : ℝ)|=(2623776899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540748139/1000000000 : ℝ)|^549 ≤ (22427733170911/50000000000000 : ℝ)^421
        have hw : |(540748139/1000000000 : ℝ)|=(540748139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s6_5 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (530537223/1000000000 : ℝ)*x 0 + (-472550507/2500000000 : ℝ)*x 1 + (5407481427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530537223/1000000000 : ℝ)^549 ≤ (21877063301503/50000000000000 : ℝ)^421 := by
    have hnat : (530537223 : ℕ)^549*50000000000000^421 ≤ 21877063301503^421*1000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530537223 1000000000 21877063301503 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (472550507/2500000000 : ℝ)^549 ≤ (11390406646081/100000000000000 : ℝ)^421 := by
    have hnat : (472550507 : ℕ)^549*100000000000000^421 ≤ 11390406646081^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472550507 2500000000 11390406646081 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407481427/10000000000 : ℝ)^549 ≤ (8971093348411/20000000000000 : ℝ)^421 := by
    have hnat : (5407481427 : ℕ)^549*20000000000000^421 ≤ 8971093348411^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407481427 10000000000 8971093348411 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530537223/1000000000 : ℝ), (-472550507/2500000000 : ℝ), (5407481427/10000000000 : ℝ)] ![(21877063301503/50000000000000 : ℝ), (11390406646081/100000000000000 : ℝ), (8971093348411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530537223/1000000000 : ℝ)|^549 ≤ (21877063301503/50000000000000 : ℝ)^421
        have hw : |(530537223/1000000000 : ℝ)|=(530537223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-472550507/2500000000 : ℝ)|^549 ≤ (11390406646081/100000000000000 : ℝ)^421
        have hw : |(-472550507/2500000000 : ℝ)|=(472550507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407481427/10000000000 : ℝ)|^549 ≤ (8971093348411/20000000000000 : ℝ)^421
        have hw : |(5407481427/10000000000 : ℝ)|=(5407481427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s6_6 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1326343071/2500000000 : ℝ)*x 0 + (5407481433/10000000000 : ℝ)*x 1 + (-378040389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326343071/2500000000 : ℝ)^549 ≤ (43754127183753/100000000000000 : ℝ)^421 := by
    have hnat : (1326343071 : ℕ)^549*100000000000000^421 ≤ 43754127183753^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326343071 2500000000 43754127183753 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407481433/10000000000 : ℝ)^549 ≤ (44855466806957/100000000000000 : ℝ)^421 := by
    have hnat : (5407481433 : ℕ)^549*100000000000000^421 ≤ 44855466806957^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407481433 10000000000 44855466806957 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (378040389/2000000000 : ℝ)^549 ≤ (5695202996927/50000000000000 : ℝ)^421 := by
    have hnat : (378040389 : ℕ)^549*50000000000000^421 ≤ 5695202996927^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378040389 2000000000 5695202996927 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326343071/2500000000 : ℝ), (5407481433/10000000000 : ℝ), (-378040389/2000000000 : ℝ)] ![(43754127183753/100000000000000 : ℝ), (44855466806957/100000000000000 : ℝ), (5695202996927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326343071/2500000000 : ℝ)|^549 ≤ (43754127183753/100000000000000 : ℝ)^421
        have hw : |(1326343071/2500000000 : ℝ)|=(1326343071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407481433/10000000000 : ℝ)|^549 ≤ (44855466806957/100000000000000 : ℝ)^421
        have hw : |(5407481433/10000000000 : ℝ)|=(5407481433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-378040389/2000000000 : ℝ)|^549 ≤ (5695202996927/50000000000000 : ℝ)^421
        have hw : |(-378040389/2000000000 : ℝ)|=(378040389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s6_7 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1075912029/2500000000 : ℝ)*x 0 + (4479981393/10000000000 : ℝ)*x 1 + (2066812039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075912029/2500000000 : ℝ)^549 ≤ (33304982653809/100000000000000 : ℝ)^421 := by
    have hnat : (1075912029 : ℕ)^549*100000000000000^421 ≤ 33304982653809^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075912029 2500000000 33304982653809 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479981393/10000000000 : ℝ)^549 ≤ (17547729427599/50000000000000 : ℝ)^421 := by
    have hnat : (4479981393 : ℕ)^549*50000000000000^421 ≤ 17547729427599^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479981393 10000000000 17547729427599 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066812039/5000000000 : ℝ)^549 ≤ (15799779235427/50000000000000 : ℝ)^421 := by
    have hnat : (2066812039 : ℕ)^549*50000000000000^421 ≤ 15799779235427^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066812039 5000000000 15799779235427 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075912029/2500000000 : ℝ), (4479981393/10000000000 : ℝ), (2066812039/5000000000 : ℝ)] ![(33304982653809/100000000000000 : ℝ), (17547729427599/50000000000000 : ℝ), (15799779235427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075912029/2500000000 : ℝ)|^549 ≤ (33304982653809/100000000000000 : ℝ)^421
        have hw : |(1075912029/2500000000 : ℝ)|=(1075912029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479981393/10000000000 : ℝ)|^549 ≤ (17547729427599/50000000000000 : ℝ)^421
        have hw : |(4479981393/10000000000 : ℝ)|=(4479981393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066812039/5000000000 : ℝ)|^549 ≤ (15799779235427/50000000000000 : ℝ)^421
        have hw : |(2066812039/5000000000 : ℝ)|=(2066812039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1432_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5673/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14759/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11343/100000 : ℝ) ^ (4391/1024 : ℝ) ≤ (2210711890418559/25000000000000000000 : ℝ) := by
    have hpowers : (11343/100000 : ℝ)^4391 ≤ (2210711890418559/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11343 : ℕ)^4391*25000000000000000000^1024 ≤ 2210711890418559^1024*100000^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11343 100000 2210711890418559 25000000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11343/100000 : ℝ)) (X := (2210711890418559/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7381/50000 : ℝ) ^ (4391/1024 : ℝ) ≤ (27366749710916507/100000000000000000000 : ℝ) := by
    have hpowers : (7381/50000 : ℝ)^4391 ≤ (27366749710916507/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7381 : ℕ)^4391*100000000000000000000^1024 ≤ 27366749710916507^1024*50000^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7381 50000 27366749710916507 100000000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7381/50000 : ℝ)) (X := (27366749710916507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502210711890418559/12500000000000000000 : ℝ) ≤ (2000082482003857/2000000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (12502210711890418559/12500000000000000000 : ℝ)^1024 ≤ (2000082482003857/2000000000000000 : ℝ)^4391 := by
      have hnat : (12502210711890418559 : ℕ)^1024*2000000000000000^4391 ≤ 2000082482003857^4391*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502210711890418559 12500000000000000000 2000082482003857 2000000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000082482003857/2000000000000000 : ℝ)) (X := (12502210711890418559/12500000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036209597272590743/100000000000000000000 : ℝ) ≤ (10000844306107871/10000000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (100036209597272590743/100000000000000000000 : ℝ)^1024 ≤ (10000844306107871/10000000000000000 : ℝ)^4391 := by
      have hnat : (100036209597272590743 : ℕ)^1024*10000000000000000^4391 ≤ 10000844306107871^4391*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036209597272590743 100000000000000000000 10000844306107871 10000000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000844306107871/10000000000000000 : ℝ)) (X := (100036209597272590743/100000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027366749710916507/50000000000000000000 : ℝ) ≤ (10001276202196457/10000000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (50027366749710916507/50000000000000000000 : ℝ)^1024 ≤ (10001276202196457/10000000000000000 : ℝ)^4391 := by
      have hnat : (50027366749710916507 : ℕ)^1024*10000000000000000^4391 ≤ 10001276202196457^4391*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027366749710916507 50000000000000000000 10001276202196457 10000000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001276202196457/10000000000000000 : ℝ)) (X := (50027366749710916507/50000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2210711890418559/25000000000000000000 : ℝ) ≤ ((34181612035190273419/34190000000000000000 : ℝ)+2*(215948044293/170950000000000 : ℝ)*(11343/100000 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (34181612035190273419/34190000000000000000 : ℝ)+2*(215948044293/170950000000000 : ℝ)*(11343/100000 : ℝ)=(2000082482003857/2000000000000000 : ℝ) by norm_num, show 1+2*(2210711890418559/25000000000000000000 : ℝ)=(12502210711890418559/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27366749710916507/100000000000000000000 : ℝ)+(2210711890418559/25000000000000000000 : ℝ) ≤ ((34181612035190273419/34190000000000000000 : ℝ)+(215948044293/170950000000000 : ℝ)*((7381/50000 : ℝ)+(11343/100000 : ℝ)))^(4391/1024 : ℝ) := by
    rw [show (34181612035190273419/34190000000000000000 : ℝ)+(215948044293/170950000000000 : ℝ)*((7381/50000 : ℝ)+(11343/100000 : ℝ))=(10000844306107871/10000000000000000 : ℝ) by norm_num, show 1+(27366749710916507/100000000000000000000 : ℝ)+(2210711890418559/25000000000000000000 : ℝ)=(100036209597272590743/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27366749710916507/100000000000000000000 : ℝ) ≤ ((34181612035190273419/34190000000000000000 : ℝ)+2*(215948044293/170950000000000 : ℝ)*(7381/50000 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (34181612035190273419/34190000000000000000 : ℝ)+2*(215948044293/170950000000000 : ℝ)*(7381/50000 : ℝ)=(10001276202196457/10000000000000000 : ℝ) by norm_num, show 1+2*(27366749710916507/100000000000000000000 : ℝ)=(50027366749710916507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34181612035190273419/34190000000000000000 : ℝ)*(X 1 0+X 2 0)+(215948044293/170950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (34181612035190273419/34190000000000000000 : ℝ)) (alpha := (215948044293/170950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34181612035190273419/34190000000000000000 : ℝ)*(X 0 1+X 2 1)+(215948044293/170950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (34181612035190273419/34190000000000000000 : ℝ)) (alpha := (215948044293/170950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34181612035190273419/34190000000000000000 : ℝ)*(X 0 2+X 1 2)+(215948044293/170950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (34181612035190273419/34190000000000000000 : ℝ)) (alpha := (215948044293/170950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-984348921/5000000000 : ℝ)*X 0 0+(676008199/1250000000 : ℝ)*X 0 1+(327935789/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336816111/2500000000 : ℝ)*X 1 0+(-1025355377/5000000000 : ℝ)*X 1 1+(327935789/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336816111/2500000000 : ℝ)*X 2 0+(327935789/625000000 : ℝ)*X 2 1+(-1025355377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4303623627/10000000000 : ℝ)*X 0 0+(4132358959/10000000000 : ℝ)*X 0 1+(2240620009/5000000000 : ℝ)*X 0 2+(4303623627/10000000000 : ℝ)*X 1 0+(4132358959/10000000000 : ℝ)*X 1 1+(2240620009/5000000000 : ℝ)*X 1 2+(4303623627/10000000000 : ℝ)*X 2 0+(4132358959/10000000000 : ℝ)*X 2 1+(2240620009/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-492177291/2500000000 : ℝ)*X 0 0+(2623776899/5000000000 : ℝ)*X 0 1+(540748139/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530537223/1000000000 : ℝ)*X 1 0+(-472550507/2500000000 : ℝ)*X 1 1+(5407481427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326343071/2500000000 : ℝ)*X 2 0+(5407481433/10000000000 : ℝ)*X 2 1+(-378040389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1075912029/2500000000 : ℝ)*X 0 0+(4479981393/10000000000 : ℝ)*X 0 1+(2066812039/5000000000 : ℝ)*X 0 2+(1075912029/2500000000 : ℝ)*X 1 0+(4479981393/10000000000 : ℝ)*X 1 1+(2066812039/5000000000 : ℝ)*X 1 2+(1075912029/2500000000 : ℝ)*X 2 0+(4479981393/10000000000 : ℝ)*X 2 1+(2066812039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1712270239917916972526136627/213687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (728391341/50000000000000 : ℝ)*(base19) + (67901219/5000000000000 : ℝ)*(base23) + (13202169/25000000000000 : ℝ)*(lower2) + (199641967/100000000000000 : ℝ)*(upper3) + (127840101/100000000000000 : ℝ)*(upper5) + (1134249253448411/25000000000000 : ℝ)*(major0) + (1134249253448411/25000000000000 : ℝ)*(major1) + (1134249253448411/25000000000000 : ℝ)*(major2) + (3103813812914793/50000000000000 : ℝ)*(sp0) + (1241531373920491/20000000000000 : ℝ)*(sp1) + (6207656968360757/100000000000000 : ℝ)*(sp2) + (2866320105270031/100000000000000 : ℝ)*(sp3) + (959392361/3125000000000 : ℝ)*(sp4) + (1532883331/10000000000000 : ℝ)*(sp7) + (143316771705167/5000000000000 : ℝ)*(f.failure) + (3103829163192569/50000000000000 : ℝ)*(f.sum) + (90197237795031/17095000000000000000000000000 : ℝ)*base66 + (11113823103907562791/854750000000000000000000000000000 : ℝ)*base68 + (8936319696187209/854750000000000000000000000000000 : ℝ)*base69 + (8717041237045062791/854750000000000000000000000000000 : ℝ)*base72 + (48957653527071/17095000000000000000000000000 : ℝ)*base74 + (5133035374539812791/854750000000000000000000000000000 : ℝ)*base76 + (6011256678763062791/854750000000000000000000000000000 : ℝ)*base78 + (6006798663467562791/854750000000000000000000000000000 : ℝ)*base80 + (1852541627463/534218750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2265291/500000000000000000000 : ℝ)*base90 + (2265291/500000000000000000000 : ℝ)*base92 + (2265291/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19329107429890225636575772689/1709500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (227995957/12500000000000 : ℝ)*(base19) + (2067940083/100000000000000 : ℝ)*(base23) + (603534663/100000000000000 : ℝ)*(lower1) + (257261173/100000000000000 : ℝ)*(upper3) + (65416451/100000000000000 : ℝ)*(lower4) + (113700577/50000000000000 : ℝ)*(upper5) + (4569982609169777/100000000000000 : ℝ)*(major0) + (4569982609169777/100000000000000 : ℝ)*(major1) + (4569982609169777/100000000000000 : ℝ)*(major2) + (7222103229/100000000000000 : ℝ)*(sp2) + (3126395060395717/50000000000000 : ℝ)*(sp4) + (3126394148411889/50000000000000 : ℝ)*(sp5) + (3126390415374061/50000000000000 : ℝ)*(sp6) + (721793680163041/25000000000000 : ℝ)*(sp7) + (721793680163041/25000000000000 : ℝ)*(f.failure) + (3126395060395717/50000000000000 : ℝ)*(f.sum) + (1785500313119/8547500000000000000000000000 : ℝ)*base66 + (110075993525257457563/3419000000000000000000000000000000 : ℝ)*base67 + (9653855564034542437/3419000000000000000000000000000000 : ℝ)*base70 + (86414608526837457563/3419000000000000000000000000000000 : ℝ)*base71 + (18988849527931/8547500000000000000000000000 : ℝ)*base73 + (731748563181408542437/3419000000000000000000000000000000 : ℝ)*base76 + (15363056631058542437/3419000000000000000000000000000000 : ℝ)*base78 + (17203308853152542437/3419000000000000000000000000000000 : ℝ)*base80 + (33140772891951/8547500000000000000000000000 : ℝ)*base81 + (18088293/2500000000000000000000 : ℝ)*base90 + (18088293/2500000000000000000000 : ℝ)*base92 + (18088293/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1432_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1432_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1432_s7_0 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1968699793/10000000000 : ℝ)*x 0 + (1352011341/2500000000 : ℝ)*x 1 + (5246991591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968699793/10000000000 : ℝ)^549 ≤ (12011112583913/100000000000000 : ℝ)^421 := by
    have hnat : (1968699793 : ℕ)^549*100000000000000^421 ≤ 12011112583913^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968699793 10000000000 12011112583913 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352011341/2500000000 : ℝ)^549 ≤ (44861566998141/100000000000000 : ℝ)^421 := by
    have hnat : (1352011341 : ℕ)^549*100000000000000^421 ≤ 44861566998141^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352011341 2500000000 44861566998141 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246991591/10000000000 : ℝ)^549 ≤ (8625464082197/20000000000000 : ℝ)^421 := by
    have hnat : (5246991591 : ℕ)^549*20000000000000^421 ≤ 8625464082197^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246991591 10000000000 8625464082197 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1968699793/10000000000 : ℝ), (1352011341/2500000000 : ℝ), (5246991591/10000000000 : ℝ)] ![(12011112583913/100000000000000 : ℝ), (44861566998141/100000000000000 : ℝ), (8625464082197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1968699793/10000000000 : ℝ)|^549 ≤ (12011112583913/100000000000000 : ℝ)^421
        have hw : |(-1968699793/10000000000 : ℝ)|=(1968699793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352011341/2500000000 : ℝ)|^549 ≤ (44861566998141/100000000000000 : ℝ)^421
        have hw : |(1352011341/2500000000 : ℝ)|=(1352011341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246991591/10000000000 : ℝ)|^549 ≤ (8625464082197/20000000000000 : ℝ)^421
        have hw : |(5246991591/10000000000 : ℝ)|=(5246991591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s7_1 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1336814577/2500000000 : ℝ)*x 0 + (-1025345363/5000000000 : ℝ)*x 1 + (5246993847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336814577/2500000000 : ℝ)^549 ≤ (44205133392759/100000000000000 : ℝ)^421 := by
    have hnat : (1336814577 : ℕ)^549*100000000000000^421 ≤ 44205133392759^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336814577 2500000000 44205133392759 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025345363/5000000000 : ℝ)^549 ≤ (12667521999633/100000000000000 : ℝ)^421 := by
    have hnat : (1025345363 : ℕ)^549*100000000000000^421 ≤ 12667521999633^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025345363 5000000000 12667521999633 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246993847/10000000000 : ℝ)^549 ≤ (4312734459183/10000000000000 : ℝ)^421 := by
    have hnat : (5246993847 : ℕ)^549*10000000000000^421 ≤ 4312734459183^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246993847 10000000000 4312734459183 10000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336814577/2500000000 : ℝ), (-1025345363/5000000000 : ℝ), (5246993847/10000000000 : ℝ)] ![(44205133392759/100000000000000 : ℝ), (12667521999633/100000000000000 : ℝ), (4312734459183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336814577/2500000000 : ℝ)|^549 ≤ (44205133392759/100000000000000 : ℝ)^421
        have hw : |(1336814577/2500000000 : ℝ)|=(1336814577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025345363/5000000000 : ℝ)|^549 ≤ (12667521999633/100000000000000 : ℝ)^421
        have hw : |(-1025345363/5000000000 : ℝ)|=(1025345363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246993847/10000000000 : ℝ)|^549 ≤ (4312734459183/10000000000000 : ℝ)^421
        have hw : |(5246993847/10000000000 : ℝ)|=(5246993847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s7_2 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347259929/10000000000 : ℝ)*x 0 + (2623495743/5000000000 : ℝ)*x 1 + (-1025345849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347259929/10000000000 : ℝ)^549 ≤ (2762821929229/6250000000000 : ℝ)^421 := by
    have hnat : (5347259929 : ℕ)^549*6250000000000^421 ≤ 2762821929229^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347259929 10000000000 2762821929229 6250000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623495743/5000000000 : ℝ)^549 ≤ (21563659642773/50000000000000 : ℝ)^421 := by
    have hnat : (2623495743 : ℕ)^549*50000000000000^421 ≤ 21563659642773^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623495743 5000000000 21563659642773 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025345849/5000000000 : ℝ)^549 ≤ (6333764914693/50000000000000 : ℝ)^421 := by
    have hnat : (1025345849 : ℕ)^549*50000000000000^421 ≤ 6333764914693^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025345849 5000000000 6333764914693 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347259929/10000000000 : ℝ), (2623495743/5000000000 : ℝ), (-1025345849/5000000000 : ℝ)] ![(2762821929229/6250000000000 : ℝ), (21563659642773/50000000000000 : ℝ), (6333764914693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347259929/10000000000 : ℝ)|^549 ≤ (2762821929229/6250000000000 : ℝ)^421
        have hw : |(5347259929/10000000000 : ℝ)|=(5347259929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623495743/5000000000 : ℝ)|^549 ≤ (21563659642773/50000000000000 : ℝ)^421
        have hw : |(2623495743/5000000000 : ℝ)|=(2623495743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025345849/5000000000 : ℝ)|^549 ≤ (6333764914693/50000000000000 : ℝ)^421
        have hw : |(-1025345849/5000000000 : ℝ)|=(1025345849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s7_3 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4303625093/10000000000 : ℝ)*x 0 + (1033101191/2500000000 : ℝ)*x 1 + (112029847/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303625093/10000000000 : ℝ)^549 ≤ (33304750313659/100000000000000 : ℝ)^421 := by
    have hnat : (4303625093 : ℕ)^549*100000000000000^421 ≤ 33304750313659^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303625093 10000000000 33304750313659 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033101191/2500000000 : ℝ)^549 ≤ (1579370199563/5000000000000 : ℝ)^421 := by
    have hnat : (1033101191 : ℕ)^549*5000000000000^421 ≤ 1579370199563^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033101191 2500000000 1579370199563 5000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112029847/250000000 : ℝ)^549 ≤ (3510784567789/10000000000000 : ℝ)^421 := by
    have hnat : (112029847 : ℕ)^549*10000000000000^421 ≤ 3510784567789^421*250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112029847 250000000 3510784567789 10000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303625093/10000000000 : ℝ), (1033101191/2500000000 : ℝ), (112029847/250000000 : ℝ)] ![(33304750313659/100000000000000 : ℝ), (1579370199563/5000000000000 : ℝ), (3510784567789/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303625093/10000000000 : ℝ)|^549 ≤ (33304750313659/100000000000000 : ℝ)^421
        have hw : |(4303625093/10000000000 : ℝ)|=(4303625093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033101191/2500000000 : ℝ)|^549 ≤ (1579370199563/5000000000000 : ℝ)^421
        have hw : |(1033101191/2500000000 : ℝ)|=(1033101191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112029847/250000000 : ℝ)|^549 ≤ (3510784567789/10000000000000 : ℝ)^421
        have hw : |(112029847/250000000 : ℝ)|=(112029847/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s7_4 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1968711147/10000000000 : ℝ)*x 0 + (2623786829/5000000000 : ℝ)*x 1 + (1351865063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968711147/10000000000 : ℝ)^549 ≤ (6005601458127/50000000000000 : ℝ)^421 := by
    have hnat : (1968711147 : ℕ)^549*50000000000000^421 ≤ 6005601458127^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968711147 10000000000 6005601458127 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623786829/5000000000 : ℝ)^549 ≤ (43133559377537/100000000000000 : ℝ)^421 := by
    have hnat : (2623786829 : ℕ)^549*100000000000000^421 ≤ 43133559377537^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623786829 5000000000 43133559377537 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351865063/2500000000 : ℝ)^549 ≤ (5606904711279/12500000000000 : ℝ)^421 := by
    have hnat : (1351865063 : ℕ)^549*12500000000000^421 ≤ 5606904711279^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351865063 2500000000 5606904711279 12500000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1968711147/10000000000 : ℝ), (2623786829/5000000000 : ℝ), (1351865063/2500000000 : ℝ)] ![(6005601458127/50000000000000 : ℝ), (43133559377537/100000000000000 : ℝ), (5606904711279/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1968711147/10000000000 : ℝ)|^549 ≤ (6005601458127/50000000000000 : ℝ)^421
        have hw : |(-1968711147/10000000000 : ℝ)|=(1968711147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623786829/5000000000 : ℝ)|^549 ≤ (43133559377537/100000000000000 : ℝ)^421
        have hw : |(2623786829/5000000000 : ℝ)|=(2623786829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351865063/2500000000 : ℝ)|^549 ≤ (5606904711279/12500000000000 : ℝ)^421
        have hw : |(1351865063/2500000000 : ℝ)|=(1351865063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s7_5 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (663172209/1250000000 : ℝ)*x 0 + (-1890223741/10000000000 : ℝ)*x 1 + (2703730121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663172209/1250000000 : ℝ)^549 ≤ (43754185129433/100000000000000 : ℝ)^421 := by
    have hnat : (663172209 : ℕ)^549*100000000000000^421 ≤ 43754185129433^421*1250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663172209 1250000000 43754185129433 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1890223741/10000000000 : ℝ)^549 ≤ (11390577270759/100000000000000 : ℝ)^421 := by
    have hnat : (1890223741 : ℕ)^549*100000000000000^421 ≤ 11390577270759^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890223741 10000000000 11390577270759 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703730121/5000000000 : ℝ)^549 ≤ (44855237582061/100000000000000 : ℝ)^421 := by
    have hnat : (2703730121 : ℕ)^549*100000000000000^421 ≤ 44855237582061^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703730121 5000000000 44855237582061 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663172209/1250000000 : ℝ), (-1890223741/10000000000 : ℝ), (2703730121/5000000000 : ℝ)] ![(43754185129433/100000000000000 : ℝ), (11390577270759/100000000000000 : ℝ), (44855237582061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663172209/1250000000 : ℝ)|^549 ≤ (43754185129433/100000000000000 : ℝ)^421
        have hw : |(663172209/1250000000 : ℝ)|=(663172209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1890223741/10000000000 : ℝ)|^549 ≤ (11390577270759/100000000000000 : ℝ)^421
        have hw : |(-1890223741/10000000000 : ℝ)|=(1890223741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703730121/5000000000 : ℝ)|^549 ≤ (44855237582061/100000000000000 : ℝ)^421
        have hw : |(2703730121/5000000000 : ℝ)|=(2703730121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s7_6 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305377651/10000000000 : ℝ)*x 0 + (5407460241/10000000000 : ℝ)*x 1 + (-1890223771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305377651/10000000000 : ℝ)^549 ≤ (43754184903587/100000000000000 : ℝ)^421 := by
    have hnat : (5305377651 : ℕ)^549*100000000000000^421 ≤ 43754184903587^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305377651 10000000000 43754184903587 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407460241/10000000000 : ℝ)^549 ≤ (11213809392811/25000000000000 : ℝ)^421 := by
    have hnat : (5407460241 : ℕ)^549*25000000000000^421 ≤ 11213809392811^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407460241 10000000000 11213809392811 25000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1890223771/10000000000 : ℝ)^549 ≤ (2278115501301/20000000000000 : ℝ)^421 := by
    have hnat : (1890223771 : ℕ)^549*20000000000000^421 ≤ 2278115501301^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890223771 10000000000 2278115501301 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305377651/10000000000 : ℝ), (5407460241/10000000000 : ℝ), (-1890223771/10000000000 : ℝ)] ![(43754184903587/100000000000000 : ℝ), (11213809392811/25000000000000 : ℝ), (2278115501301/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305377651/10000000000 : ℝ)|^549 ≤ (43754184903587/100000000000000 : ℝ)^421
        have hw : |(5305377651/10000000000 : ℝ)|=(5305377651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407460241/10000000000 : ℝ)|^549 ≤ (11213809392811/25000000000000 : ℝ)^421
        have hw : |(5407460241/10000000000 : ℝ)|=(5407460241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1890223771/10000000000 : ℝ)|^549 ≤ (2278115501301/20000000000000 : ℝ)^421
        have hw : |(-1890223771/10000000000 : ℝ)|=(1890223771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_s7_7 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4303649563/10000000000 : ℝ)*x 0 + (447993673/1000000000 : ℝ)*x 1 + (4133668383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303649563/10000000000 : ℝ)^549 ≤ (6660999451289/20000000000000 : ℝ)^421 := by
    have hnat : (4303649563 : ℕ)^549*20000000000000^421 ≤ 6660999451289^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303649563 10000000000 6660999451289 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447993673/1000000000 : ℝ)^549 ≤ (2193437662213/6250000000000 : ℝ)^421 := by
    have hnat : (447993673 : ℕ)^549*6250000000000^421 ≤ 2193437662213^421*1000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447993673 1000000000 2193437662213 6250000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4133668383/10000000000 : ℝ)^549 ≤ (6320000027323/20000000000000 : ℝ)^421 := by
    have hnat : (4133668383 : ℕ)^549*20000000000000^421 ≤ 6320000027323^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133668383 10000000000 6320000027323 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303649563/10000000000 : ℝ), (447993673/1000000000 : ℝ), (4133668383/10000000000 : ℝ)] ![(6660999451289/20000000000000 : ℝ), (2193437662213/6250000000000 : ℝ), (6320000027323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303649563/10000000000 : ℝ)|^549 ≤ (6660999451289/20000000000000 : ℝ)^421
        have hw : |(4303649563/10000000000 : ℝ)|=(4303649563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447993673/1000000000 : ℝ)|^549 ≤ (2193437662213/6250000000000 : ℝ)^421
        have hw : |(447993673/1000000000 : ℝ)|=(447993673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4133668383/10000000000 : ℝ)|^549 ≤ (6320000027323/20000000000000 : ℝ)^421
        have hw : |(4133668383/10000000000 : ℝ)|=(4133668383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1432_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11347/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7379/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5673/50000 : ℝ) ^ (4391/1024 : ℝ) ≤ (4426440361289361/50000000000000000000 : ℝ) := by
    have hpowers : (5673/50000 : ℝ)^4391 ≤ (4426440361289361/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5673 : ℕ)^4391*50000000000000000000^1024 ≤ 4426440361289361^1024*50000^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5673 50000 4426440361289361 50000000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5673/50000 : ℝ)) (X := (4426440361289361/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14759/100000 : ℝ) ^ (4391/1024 : ℝ) ≤ (27342909085142973/100000000000000000000 : ℝ) := by
    have hpowers : (14759/100000 : ℝ)^4391 ≤ (27342909085142973/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14759 : ℕ)^4391*100000000000000000000^1024 ≤ 27342909085142973^1024*100000^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14759 100000 27342909085142973 100000000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14759/100000 : ℝ)) (X := (27342909085142973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004426440361289361/25000000000000000000 : ℝ) ≤ (5000206438955507/5000000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (25004426440361289361/25000000000000000000 : ℝ)^1024 ≤ (5000206438955507/5000000000000000 : ℝ)^4391 := by
      have hnat : (25004426440361289361 : ℕ)^1024*5000000000000000^4391 ≤ 5000206438955507^4391*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004426440361289361 25000000000000000000 5000206438955507 5000000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000206438955507/5000000000000000 : ℝ)) (X := (25004426440361289361/25000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007239157961544339/20000000000000000000 : ℝ) ≤ (2500210996050309/2500000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (20007239157961544339/20000000000000000000 : ℝ)^1024 ≤ (2500210996050309/2500000000000000 : ℝ)^4391 := by
      have hnat : (20007239157961544339 : ℕ)^1024*2500000000000000^4391 ≤ 2500210996050309^4391*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007239157961544339 20000000000000000000 2500210996050309 2500000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500210996050309/2500000000000000 : ℝ)) (X := (20007239157961544339/20000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027342909085142973/50000000000000000000 : ℝ) ≤ (5000637545245729/5000000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (50027342909085142973/50000000000000000000 : ℝ)^1024 ≤ (5000637545245729/5000000000000000 : ℝ)^4391 := by
      have hnat : (50027342909085142973 : ℕ)^1024*5000000000000000^4391 ≤ 5000637545245729^4391*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027342909085142973 50000000000000000000 5000637545245729 5000000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000637545245729/5000000000000000 : ℝ)) (X := (50027342909085142973/50000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4426440361289361/50000000000000000000 : ℝ) ≤ ((17060813244186286579/17065000000000000000 : ℝ)+2*(215553145111/170650000000000 : ℝ)*(5673/50000 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (17060813244186286579/17065000000000000000 : ℝ)+2*(215553145111/170650000000000 : ℝ)*(5673/50000 : ℝ)=(5000206438955507/5000000000000000 : ℝ) by norm_num, show 1+2*(4426440361289361/50000000000000000000 : ℝ)=(25004426440361289361/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27342909085142973/100000000000000000000 : ℝ)+(4426440361289361/50000000000000000000 : ℝ) ≤ ((17060813244186286579/17065000000000000000 : ℝ)+(215553145111/170650000000000 : ℝ)*((14759/100000 : ℝ)+(5673/50000 : ℝ)))^(4391/1024 : ℝ) := by
    rw [show (17060813244186286579/17065000000000000000 : ℝ)+(215553145111/170650000000000 : ℝ)*((14759/100000 : ℝ)+(5673/50000 : ℝ))=(2500210996050309/2500000000000000 : ℝ) by norm_num, show 1+(27342909085142973/100000000000000000000 : ℝ)+(4426440361289361/50000000000000000000 : ℝ)=(20007239157961544339/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27342909085142973/100000000000000000000 : ℝ) ≤ ((17060813244186286579/17065000000000000000 : ℝ)+2*(215553145111/170650000000000 : ℝ)*(14759/100000 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (17060813244186286579/17065000000000000000 : ℝ)+2*(215553145111/170650000000000 : ℝ)*(14759/100000 : ℝ)=(5000637545245729/5000000000000000 : ℝ) by norm_num, show 1+2*(27342909085142973/100000000000000000000 : ℝ)=(50027342909085142973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17060813244186286579/17065000000000000000 : ℝ)*(X 1 0+X 2 0)+(215553145111/170650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (17060813244186286579/17065000000000000000 : ℝ)) (alpha := (215553145111/170650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17060813244186286579/17065000000000000000 : ℝ)*(X 0 1+X 2 1)+(215553145111/170650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (17060813244186286579/17065000000000000000 : ℝ)) (alpha := (215553145111/170650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17060813244186286579/17065000000000000000 : ℝ)*(X 0 2+X 1 2)+(215553145111/170650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (17060813244186286579/17065000000000000000 : ℝ)) (alpha := (215553145111/170650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1968699793/10000000000 : ℝ)*X 0 0+(1352011341/2500000000 : ℝ)*X 0 1+(5246991591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336814577/2500000000 : ℝ)*X 1 0+(-1025345363/5000000000 : ℝ)*X 1 1+(5246993847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347259929/10000000000 : ℝ)*X 2 0+(2623495743/5000000000 : ℝ)*X 2 1+(-1025345849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4303625093/10000000000 : ℝ)*X 0 0+(1033101191/2500000000 : ℝ)*X 0 1+(112029847/250000000 : ℝ)*X 0 2+(4303625093/10000000000 : ℝ)*X 1 0+(1033101191/2500000000 : ℝ)*X 1 1+(112029847/250000000 : ℝ)*X 1 2+(4303625093/10000000000 : ℝ)*X 2 0+(1033101191/2500000000 : ℝ)*X 2 1+(112029847/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1968711147/10000000000 : ℝ)*X 0 0+(2623786829/5000000000 : ℝ)*X 0 1+(1351865063/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663172209/1250000000 : ℝ)*X 1 0+(-1890223741/10000000000 : ℝ)*X 1 1+(2703730121/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305377651/10000000000 : ℝ)*X 2 0+(5407460241/10000000000 : ℝ)*X 2 1+(-1890223771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4303649563/10000000000 : ℝ)*X 0 0+(447993673/1000000000 : ℝ)*X 0 1+(4133668383/10000000000 : ℝ)*X 0 2+(4303649563/10000000000 : ℝ)*X 1 0+(447993673/1000000000 : ℝ)*X 1 1+(4133668383/10000000000 : ℝ)*X 1 2+(4303649563/10000000000 : ℝ)*X 2 0+(447993673/1000000000 : ℝ)*X 2 1+(4133668383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15425737552377125391057/8532500000000000000000000000 : ℝ) := by norm_num
    linear_combination (993375633/100000000000000 : ℝ)*(base23) + (9236897/5000000000000 : ℝ)*(lower2) + (12381381/50000000000000 : ℝ)*(upper3) + (58228113/50000000000000 : ℝ)*(upper4) + (4538166353292611/100000000000000 : ℝ)*(major0) + (4538166353292611/100000000000000 : ℝ)*(major1) + (4538166353292611/100000000000000 : ℝ)*(major2) + (3104586353863551/50000000000000 : ℝ)*(sp0) + (6209258459420767/100000000000000 : ℝ)*(sp1) + (3104607943459551/50000000000000 : ℝ)*(sp2) + (1433531919340829/50000000000000 : ℝ)*(sp3) + (17150338733/20000000000000 : ℝ)*(sp4) + (2598695377/6250000000000 : ℝ)*(sp6) + (2587055027/25000000000000 : ℝ)*(sp7) + (1433537093450883/50000000000000 : ℝ)*(f.failure) + (6209258459420767/100000000000000 : ℝ)*(f.sum) + (667972883162437/17065000000000000000000000000 : ℝ)*base65 + (21280892809753732231/1706500000000000000000000000000000 : ℝ)*base68 + (11835558683057732231/1706500000000000000000000000000000 : ℝ)*base70 + (124266795974550267769/1706500000000000000000000000000000 : ℝ)*base71 + (17849293259127/4266250000000000000000000000 : ℝ)*base74 + (17891104286573232231/1706500000000000000000000000000000 : ℝ)*base76 + (4016750672449267769/1706500000000000000000000000000000 : ℝ)*base77 + (5604796964737267769/1706500000000000000000000000000000 : ℝ)*base79 + (26005912281401/8532500000000000000000000000 : ℝ)*base81 + (59358641/5000000000000000000000 : ℝ)*base89 + (59358641/5000000000000000000000 : ℝ)*base91 + (59358641/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (376453647047146304781/66660156250000000000000000 : ℝ) := by norm_num
    linear_combination (939374017/100000000000000 : ℝ)*(base19) + (1031347783/100000000000000 : ℝ)*(base23) + (160966277/50000000000000 : ℝ)*(lower1) + (103224283/100000000000000 : ℝ)*(upper3) + (59449937/100000000000000 : ℝ)*(lower4) + (60110181/50000000000000 : ℝ)*(upper5) + (571395980441317/12500000000000 : ℝ)*(major0) + (571395980441317/12500000000000 : ℝ)*(major1) + (571395980441317/12500000000000 : ℝ)*(major2) + (148027087/25000000000000 : ℝ)*(sp2) + (3127205991739767/50000000000000 : ℝ)*(sp4) + (6254411044105517/100000000000000 : ℝ)*(sp5) + (6254410360023403/100000000000000 : ℝ)*(sp6) + (4512380492713/156250000000 : ℝ)*(sp7) + (4512380492713/156250000000 : ℝ)*(f.failure) + (3127205991739767/50000000000000 : ℝ)*(f.sum) + (6890784445981/8532500000000000000000000000 : ℝ)*base65 + (2715696076866865457/213312500000000000000000000000000 : ℝ)*base68 + (311506049106384543/213312500000000000000000000000000 : ℝ)*base69 + (4228394659148384543/213312500000000000000000000000000 : ℝ)*base71 + (37322847374703/17065000000000000000000000000 : ℝ)*base74 + (6273423638362240457/213312500000000000000000000000000 : ℝ)*base76 + (442325111806177957/213312500000000000000000000000000 : ℝ)*base78 + (591281237068947043/213312500000000000000000000000000 : ℝ)*base79 + (65309591403303/17065000000000000000000000000 : ℝ)*base82 + (113949/15625000000000000000 : ℝ)*base90 + (113949/15625000000000000000 : ℝ)*base92 + (113949/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1432_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1432_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1432_box_0 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-226032377/1250000000 : ℝ)*x 0 + (2693063551/5000000000 : ℝ)*x 1 + (107722543/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226032377/1250000000 : ℝ)^549 ≤ (5375385929701/50000000000000 : ℝ)^421 := by
    have hnat : (226032377 : ℕ)^549*50000000000000^421 ≤ 5375385929701^421*1250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226032377 1250000000 5375385929701 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693063551/5000000000 : ℝ)^549 ≤ (44624613805419/100000000000000 : ℝ)^421 := by
    have hnat : (2693063551 : ℕ)^549*100000000000000^421 ≤ 44624613805419^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693063551 5000000000 44624613805419 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107722543/200000000 : ℝ)^549 ≤ (8924922864803/20000000000000 : ℝ)^421 := by
    have hnat : (107722543 : ℕ)^549*20000000000000^421 ≤ 8924922864803^421*200000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107722543 200000000 8924922864803 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-226032377/1250000000 : ℝ), (2693063551/5000000000 : ℝ), (107722543/200000000 : ℝ)] ![(5375385929701/50000000000000 : ℝ), (44624613805419/100000000000000 : ℝ), (8924922864803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-226032377/1250000000 : ℝ)|^549 ≤ (5375385929701/50000000000000 : ℝ)^421
        have hw : |(-226032377/1250000000 : ℝ)|=(226032377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693063551/5000000000 : ℝ)|^549 ≤ (44624613805419/100000000000000 : ℝ)^421
        have hw : |(2693063551/5000000000 : ℝ)|=(2693063551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107722543/200000000 : ℝ)|^549 ≤ (8924922864803/20000000000000 : ℝ)^421
        have hw : |(107722543/200000000 : ℝ)|=(107722543/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_1 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5286086501/10000000000 : ℝ)*x 0 + (-38914257/200000000 : ℝ)*x 1 + (673265893/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286086501/10000000000 : ℝ)^549 ≤ (8709366284657/20000000000000 : ℝ)^421 := by
    have hnat : (5286086501 : ℕ)^549*20000000000000^421 ≤ 8709366284657^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286086501 10000000000 8709366284657 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38914257/200000000 : ℝ)^549 ≤ (739284643673/6250000000000 : ℝ)^421 := by
    have hnat : (38914257 : ℕ)^549*6250000000000^421 ≤ 739284643673^421*200000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38914257 200000000 739284643673 6250000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673265893/1250000000 : ℝ)^549 ≤ (44624614259191/100000000000000 : ℝ)^421 := by
    have hnat : (673265893 : ℕ)^549*100000000000000^421 ≤ 44624614259191^421*1250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673265893 1250000000 44624614259191 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286086501/10000000000 : ℝ), (-38914257/200000000 : ℝ), (673265893/1250000000 : ℝ)] ![(8709366284657/20000000000000 : ℝ), (739284643673/6250000000000 : ℝ), (44624614259191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286086501/10000000000 : ℝ)|^549 ≤ (8709366284657/20000000000000 : ℝ)^421
        have hw : |(5286086501/10000000000 : ℝ)|=(5286086501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38914257/200000000 : ℝ)|^549 ≤ (739284643673/6250000000000 : ℝ)^421
        have hw : |(-38914257/200000000 : ℝ)|=(38914257/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673265893/1250000000 : ℝ)|^549 ≤ (44624614259191/100000000000000 : ℝ)^421
        have hw : |(673265893/1250000000 : ℝ)|=(673265893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_2 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1321521617/2500000000 : ℝ)*x 0 + (2693063567/5000000000 : ℝ)*x 1 + (-1945712909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321521617/2500000000 : ℝ)^549 ≤ (43546831068777/100000000000000 : ℝ)^421 := by
    have hnat : (1321521617 : ℕ)^549*100000000000000^421 ≤ 43546831068777^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321521617 2500000000 43546831068777 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693063567/5000000000 : ℝ)^549 ≤ (892492283023/2000000000000 : ℝ)^421 := by
    have hnat : (2693063567 : ℕ)^549*2000000000000^421 ≤ 892492283023^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693063567 5000000000 892492283023 2000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945712909/10000000000 : ℝ)^549 ≤ (5914277383249/50000000000000 : ℝ)^421 := by
    have hnat : (1945712909 : ℕ)^549*50000000000000^421 ≤ 5914277383249^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945712909 10000000000 5914277383249 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321521617/2500000000 : ℝ), (2693063567/5000000000 : ℝ), (-1945712909/10000000000 : ℝ)] ![(43546831068777/100000000000000 : ℝ), (892492283023/2000000000000 : ℝ), (5914277383249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321521617/2500000000 : ℝ)|^549 ≤ (43546831068777/100000000000000 : ℝ)^421
        have hw : |(1321521617/2500000000 : ℝ)|=(1321521617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693063567/5000000000 : ℝ)|^549 ≤ (892492283023/2000000000000 : ℝ)^421
        have hw : |(2693063567/5000000000 : ℝ)|=(2693063567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1945712909/10000000000 : ℝ)|^549 ≤ (5914277383249/50000000000000 : ℝ)^421
        have hw : |(-1945712909/10000000000 : ℝ)|=(1945712909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_3 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2224930211/5000000000 : ℝ)*x 0 + (4234210331/10000000000 : ℝ)*x 1 + (4234210357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2224930211/5000000000 : ℝ)^549 ≤ (6957613858133/20000000000000 : ℝ)^421 := by
    have hnat : (2224930211 : ℕ)^549*20000000000000^421 ≤ 6957613858133^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224930211 5000000000 6957613858133 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234210331/10000000000 : ℝ)^549 ≤ (16302982610417/50000000000000 : ℝ)^421 := by
    have hnat : (4234210331 : ℕ)^549*50000000000000^421 ≤ 16302982610417^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234210331 10000000000 16302982610417 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234210357/10000000000 : ℝ)^549 ≤ (32605965481923/100000000000000 : ℝ)^421 := by
    have hnat : (4234210357 : ℕ)^549*100000000000000^421 ≤ 32605965481923^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234210357 10000000000 32605965481923 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2224930211/5000000000 : ℝ), (4234210331/10000000000 : ℝ), (4234210357/10000000000 : ℝ)] ![(6957613858133/20000000000000 : ℝ), (16302982610417/50000000000000 : ℝ), (32605965481923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2224930211/5000000000 : ℝ)|^549 ≤ (6957613858133/20000000000000 : ℝ)^421
        have hw : |(2224930211/5000000000 : ℝ)|=(2224930211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234210331/10000000000 : ℝ)|^549 ≤ (16302982610417/50000000000000 : ℝ)^421
        have hw : |(4234210331/10000000000 : ℝ)|=(4234210331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234210357/10000000000 : ℝ)|^549 ≤ (32605965481923/100000000000000 : ℝ)^421
        have hw : |(4234210357/10000000000 : ℝ)|=(4234210357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_4 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-213187567/1000000000 : ℝ)*x 0 + (1316642811/2500000000 : ℝ)*x 1 + (5266571477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213187567/1000000000 : ℝ)^549 ≤ (13325391346893/100000000000000 : ℝ)^421 := by
    have hnat : (213187567 : ℕ)^549*100000000000000^421 ≤ 13325391346893^421*1000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213187567 1000000000 13325391346893 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316642811/2500000000 : ℝ)^549 ≤ (43337303068429/100000000000000 : ℝ)^421 := by
    have hnat : (1316642811 : ℕ)^549*100000000000000^421 ≤ 43337303068429^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316642811 2500000000 43337303068429 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266571477/10000000000 : ℝ)^549 ≤ (2166865278433/5000000000000 : ℝ)^421 := by
    have hnat : (5266571477 : ℕ)^549*5000000000000^421 ≤ 2166865278433^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266571477 10000000000 2166865278433 5000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213187567/1000000000 : ℝ), (1316642811/2500000000 : ℝ), (5266571477/10000000000 : ℝ)] ![(13325391346893/100000000000000 : ℝ), (43337303068429/100000000000000 : ℝ), (2166865278433/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213187567/1000000000 : ℝ)|^549 ≤ (13325391346893/100000000000000 : ℝ)^421
        have hw : |(-213187567/1000000000 : ℝ)|=(213187567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316642811/2500000000 : ℝ)|^549 ≤ (43337303068429/100000000000000 : ℝ)^421
        have hw : |(1316642811/2500000000 : ℝ)|=(1316642811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266571477/10000000000 : ℝ)|^549 ≤ (2166865278433/5000000000000 : ℝ)^421
        have hw : |(5266571477/10000000000 : ℝ)|=(5266571477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_5 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (335609239/625000000 : ℝ)*x 0 + (-398854489/2000000000 : ℝ)*x 1 + (1053314167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335609239/625000000 : ℝ)^549 ≤ (44447732507381/100000000000000 : ℝ)^421 := by
    have hnat : (335609239 : ℕ)^549*100000000000000^421 ≤ 44447732507381^421*625000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335609239 625000000 44447732507381 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398854489/2000000000 : ℝ)^549 ≤ (12214968789461/100000000000000 : ℝ)^421 := by
    have hnat : (398854489 : ℕ)^549*100000000000000^421 ≤ 12214968789461^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398854489 2000000000 12214968789461 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053314167/2000000000 : ℝ)^549 ≤ (10834324669903/25000000000000 : ℝ)^421 := by
    have hnat : (1053314167 : ℕ)^549*25000000000000^421 ≤ 10834324669903^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053314167 2000000000 10834324669903 25000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335609239/625000000 : ℝ), (-398854489/2000000000 : ℝ), (1053314167/2000000000 : ℝ)] ![(44447732507381/100000000000000 : ℝ), (12214968789461/100000000000000 : ℝ), (10834324669903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335609239/625000000 : ℝ)|^549 ≤ (44447732507381/100000000000000 : ℝ)^421
        have hw : |(335609239/625000000 : ℝ)|=(335609239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-398854489/2000000000 : ℝ)|^549 ≤ (12214968789461/100000000000000 : ℝ)^421
        have hw : |(-398854489/2000000000 : ℝ)|=(398854489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053314167/2000000000 : ℝ)|^549 ≤ (10834324669903/25000000000000 : ℝ)^421
        have hw : |(1053314167/2000000000 : ℝ)|=(1053314167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_6 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (83902299/156250000 : ℝ)*x 0 + (5266572111/10000000000 : ℝ)*x 1 + (-997135831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83902299/156250000 : ℝ)^549 ≤ (5555965635131/12500000000000 : ℝ)^421 := by
    have hnat : (83902299 : ℕ)^549*12500000000000^421 ≤ 5555965635131^421*156250000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83902299 156250000 5555965635131 12500000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266572111/10000000000 : ℝ)^549 ≤ (43337312371863/100000000000000 : ℝ)^421 := by
    have hnat : (5266572111 : ℕ)^549*100000000000000^421 ≤ 43337312371863^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266572111 10000000000 43337312371863 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (997135831/5000000000 : ℝ)^549 ≤ (12214962535433/100000000000000 : ℝ)^421 := by
    have hnat : (997135831 : ℕ)^549*100000000000000^421 ≤ 12214962535433^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997135831 5000000000 12214962535433 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83902299/156250000 : ℝ), (5266572111/10000000000 : ℝ), (-997135831/5000000000 : ℝ)] ![(5555965635131/12500000000000 : ℝ), (43337312371863/100000000000000 : ℝ), (12214962535433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83902299/156250000 : ℝ)|^549 ≤ (5555965635131/12500000000000 : ℝ)^421
        have hw : |(83902299/156250000 : ℝ)|=(83902299/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266572111/10000000000 : ℝ)|^549 ≤ (43337312371863/100000000000000 : ℝ)^421
        have hw : |(5266572111/10000000000 : ℝ)|=(5266572111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-997135831/5000000000 : ℝ)|^549 ≤ (12214962535433/100000000000000 : ℝ)^421
        have hw : |(-997135831/5000000000 : ℝ)|=(997135831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_7 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (519542211/1250000000 : ℝ)*x 0 + (21904603/50000000 : ℝ)*x 1 + (1095230303/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519542211/1250000000 : ℝ)^549 ≤ (6365234689871/20000000000000 : ℝ)^421 := by
    have hnat : (519542211 : ℕ)^549*20000000000000^421 ≤ 6365234689871^421*1250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519542211 1250000000 6365234689871 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21904603/50000000 : ℝ)^549 ≤ (8521727540559/25000000000000 : ℝ)^421 := by
    have hnat : (21904603 : ℕ)^549*25000000000000^421 ≤ 8521727540559^421*50000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21904603 50000000 8521727540559 25000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095230303/2500000000 : ℝ)^549 ≤ (34086916371841/100000000000000 : ℝ)^421 := by
    have hnat : (1095230303 : ℕ)^549*100000000000000^421 ≤ 34086916371841^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095230303 2500000000 34086916371841 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519542211/1250000000 : ℝ), (21904603/50000000 : ℝ), (1095230303/2500000000 : ℝ)] ![(6365234689871/20000000000000 : ℝ), (8521727540559/25000000000000 : ℝ), (34086916371841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519542211/1250000000 : ℝ)|^549 ≤ (6365234689871/20000000000000 : ℝ)^421
        have hw : |(519542211/1250000000 : ℝ)|=(519542211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21904603/50000000 : ℝ)|^549 ≤ (8521727540559/25000000000000 : ℝ)^421
        have hw : |(21904603/50000000 : ℝ)|=(21904603/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095230303/2500000000 : ℝ)|^549 ≤ (34086916371841/100000000000000 : ℝ)^421
        have hw : |(1095230303/2500000000 : ℝ)|=(1095230303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_8 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-515926489/2500000000 : ℝ)*x 0 + (5183861527/10000000000 : ℝ)*x 1 + (5400099367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515926489/2500000000 : ℝ)^549 ≤ (3193116148593/25000000000000 : ℝ)^421 := by
    have hnat : (515926489 : ℕ)^549*25000000000000^421 ≤ 3193116148593^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515926489 2500000000 3193116148593 25000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183861527/10000000000 : ℝ)^549 ≤ (8490380901477/20000000000000 : ℝ)^421 := by
    have hnat : (5183861527 : ℕ)^549*20000000000000^421 ≤ 8490380901477^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183861527 10000000000 8490380901477 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400099367/10000000000 : ℝ)^549 ≤ (22387815442121/50000000000000 : ℝ)^421 := by
    have hnat : (5400099367 : ℕ)^549*50000000000000^421 ≤ 22387815442121^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400099367 10000000000 22387815442121 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-515926489/2500000000 : ℝ), (5183861527/10000000000 : ℝ), (5400099367/10000000000 : ℝ)] ![(3193116148593/25000000000000 : ℝ), (8490380901477/20000000000000 : ℝ), (22387815442121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-515926489/2500000000 : ℝ)|^549 ≤ (3193116148593/25000000000000 : ℝ)^421
        have hw : |(-515926489/2500000000 : ℝ)|=(515926489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183861527/10000000000 : ℝ)|^549 ≤ (8490380901477/20000000000000 : ℝ)^421
        have hw : |(5183861527/10000000000 : ℝ)|=(5183861527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400099367/10000000000 : ℝ)|^549 ≤ (22387815442121/50000000000000 : ℝ)^421
        have hw : |(5400099367/10000000000 : ℝ)|=(5400099367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_9 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2638152803/5000000000 : ℝ)*x 0 + (-1939911921/10000000000 : ℝ)*x 1 + (5400098771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638152803/5000000000 : ℝ)^549 ≤ (5430223498663/12500000000000 : ℝ)^421 := by
    have hnat : (2638152803 : ℕ)^549*12500000000000^421 ≤ 5430223498663^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638152803 5000000000 5430223498663 12500000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1939911921/10000000000 : ℝ)^549 ≤ (11782587558807/100000000000000 : ℝ)^421 := by
    have hnat : (1939911921 : ℕ)^549*100000000000000^421 ≤ 11782587558807^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939911921 10000000000 11782587558807 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400098771/10000000000 : ℝ)^549 ≤ (44775624439931/100000000000000 : ℝ)^421 := by
    have hnat : (5400098771 : ℕ)^549*100000000000000^421 ≤ 44775624439931^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400098771 10000000000 44775624439931 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638152803/5000000000 : ℝ), (-1939911921/10000000000 : ℝ), (5400098771/10000000000 : ℝ)] ![(5430223498663/12500000000000 : ℝ), (11782587558807/100000000000000 : ℝ), (44775624439931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638152803/5000000000 : ℝ)|^549 ≤ (5430223498663/12500000000000 : ℝ)^421
        have hw : |(2638152803/5000000000 : ℝ)|=(2638152803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1939911921/10000000000 : ℝ)|^549 ≤ (11782587558807/100000000000000 : ℝ)^421
        have hw : |(-1939911921/10000000000 : ℝ)|=(1939911921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400098771/10000000000 : ℝ)|^549 ≤ (44775624439931/100000000000000 : ℝ)^421
        have hw : |(5400098771/10000000000 : ℝ)|=(5400098771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_10 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1055261061/2000000000 : ℝ)*x 0 + (2700049423/5000000000 : ℝ)*x 1 + (-969956113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055261061/2000000000 : ℝ)^549 ≤ (21720892378789/50000000000000 : ℝ)^421 := by
    have hnat : (1055261061 : ℕ)^549*50000000000000^421 ≤ 21720892378789^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055261061 2000000000 21720892378789 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700049423/5000000000 : ℝ)^549 ≤ (11193906312719/25000000000000 : ℝ)^421 := by
    have hnat : (2700049423 : ℕ)^549*25000000000000^421 ≤ 11193906312719^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700049423 5000000000 11193906312719 25000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (969956113/5000000000 : ℝ)^549 ≤ (11782589974539/100000000000000 : ℝ)^421 := by
    have hnat : (969956113 : ℕ)^549*100000000000000^421 ≤ 11782589974539^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969956113 5000000000 11782589974539 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055261061/2000000000 : ℝ), (2700049423/5000000000 : ℝ), (-969956113/5000000000 : ℝ)] ![(21720892378789/50000000000000 : ℝ), (11193906312719/25000000000000 : ℝ), (11782589974539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055261061/2000000000 : ℝ)|^549 ≤ (21720892378789/50000000000000 : ℝ)^421
        have hw : |(1055261061/2000000000 : ℝ)|=(1055261061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700049423/5000000000 : ℝ)|^549 ≤ (11193906312719/25000000000000 : ℝ)^421
        have hw : |(2700049423/5000000000 : ℝ)|=(2700049423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-969956113/5000000000 : ℝ)|^549 ≤ (11782589974539/100000000000000 : ℝ)^421
        have hw : |(-969956113/5000000000 : ℝ)|=(969956113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_11 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4483605877/10000000000 : ℝ)*x 0 + (1054262521/2500000000 : ℝ)*x 1 + (4217051021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4483605877/10000000000 : ℝ)^549 ≤ (17566244889679/50000000000000 : ℝ)^421 := by
    have hnat : (4483605877 : ℕ)^549*50000000000000^421 ≤ 17566244889679^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483605877 10000000000 17566244889679 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054262521/2500000000 : ℝ)^549 ≤ (32433750403741/100000000000000 : ℝ)^421 := by
    have hnat : (1054262521 : ℕ)^549*100000000000000^421 ≤ 32433750403741^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054262521 2500000000 32433750403741 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4217051021/10000000000 : ℝ)^549 ≤ (32433759801369/100000000000000 : ℝ)^421 := by
    have hnat : (4217051021 : ℕ)^549*100000000000000^421 ≤ 32433759801369^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217051021 10000000000 32433759801369 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4483605877/10000000000 : ℝ), (1054262521/2500000000 : ℝ), (4217051021/10000000000 : ℝ)] ![(17566244889679/50000000000000 : ℝ), (32433750403741/100000000000000 : ℝ), (32433759801369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4483605877/10000000000 : ℝ)|^549 ≤ (17566244889679/50000000000000 : ℝ)^421
        have hw : |(4483605877/10000000000 : ℝ)|=(4483605877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054262521/2500000000 : ℝ)|^549 ≤ (32433750403741/100000000000000 : ℝ)^421
        have hw : |(1054262521/2500000000 : ℝ)|=(1054262521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4217051021/10000000000 : ℝ)|^549 ≤ (32433759801369/100000000000000 : ℝ)^421
        have hw : |(4217051021/10000000000 : ℝ)|=(4217051021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_12 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1876604417/10000000000 : ℝ)*x 0 + (683352367/1250000000 : ℝ)*x 1 + (262772177/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1876604417/10000000000 : ℝ)^549 ≤ (5641835697979/50000000000000 : ℝ)^421 := by
    have hnat : (1876604417 : ℕ)^549*50000000000000^421 ≤ 5641835697979^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876604417 10000000000 5641835697979 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683352367/1250000000 : ℝ)^549 ≤ (45498394135099/100000000000000 : ℝ)^421 := by
    have hnat : (683352367 : ℕ)^549*100000000000000^421 ≤ 45498394135099^421*1250000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683352367 1250000000 45498394135099 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262772177/500000000 : ℝ)^549 ≤ (21608967228101/50000000000000 : ℝ)^421 := by
    have hnat : (262772177 : ℕ)^549*50000000000000^421 ≤ 21608967228101^421*500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262772177 500000000 21608967228101 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1876604417/10000000000 : ℝ), (683352367/1250000000 : ℝ), (262772177/500000000 : ℝ)] ![(5641835697979/50000000000000 : ℝ), (45498394135099/100000000000000 : ℝ), (21608967228101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1876604417/10000000000 : ℝ)|^549 ≤ (5641835697979/50000000000000 : ℝ)^421
        have hw : |(-1876604417/10000000000 : ℝ)|=(1876604417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683352367/1250000000 : ℝ)|^549 ≤ (45498394135099/100000000000000 : ℝ)^421
        have hw : |(683352367/1250000000 : ℝ)|=(683352367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262772177/500000000 : ℝ)|^549 ≤ (21608967228101/50000000000000 : ℝ)^421
        have hw : |(262772177/500000000 : ℝ)|=(262772177/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_13 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1075506403/2000000000 : ℝ)*x 0 + (-999346191/5000000000 : ℝ)*x 1 + (1313861057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075506403/2000000000 : ℝ)^549 ≤ (44531774262939/100000000000000 : ℝ)^421 := by
    have hnat : (1075506403 : ℕ)^549*100000000000000^421 ≤ 44531774262939^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075506403 2000000000 44531774262939 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999346191/5000000000 : ℝ)^549 ≤ (12250283888163/100000000000000 : ℝ)^421 := by
    have hnat : (999346191 : ℕ)^549*100000000000000^421 ≤ 12250283888163^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999346191 5000000000 12250283888163 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313861057/2500000000 : ℝ)^549 ≤ (337640170579/781250000000 : ℝ)^421 := by
    have hnat : (1313861057 : ℕ)^549*781250000000^421 ≤ 337640170579^421*2500000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313861057 2500000000 337640170579 781250000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075506403/2000000000 : ℝ), (-999346191/5000000000 : ℝ), (1313861057/2500000000 : ℝ)] ![(44531774262939/100000000000000 : ℝ), (12250283888163/100000000000000 : ℝ), (337640170579/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075506403/2000000000 : ℝ)|^549 ≤ (44531774262939/100000000000000 : ℝ)^421
        have hw : |(1075506403/2000000000 : ℝ)|=(1075506403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-999346191/5000000000 : ℝ)|^549 ≤ (12250283888163/100000000000000 : ℝ)^421
        have hw : |(-999346191/5000000000 : ℝ)|=(999346191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313861057/2500000000 : ℝ)|^549 ≤ (337640170579/781250000000 : ℝ)^421
        have hw : |(1313861057/2500000000 : ℝ)|=(1313861057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_14 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2688765923/5000000000 : ℝ)*x 0 + (2627722131/5000000000 : ℝ)*x 1 + (-399738513/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688765923/5000000000 : ℝ)^549 ≤ (8906354487587/20000000000000 : ℝ)^421 := by
    have hnat : (2688765923 : ℕ)^549*20000000000000^421 ≤ 8906354487587^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688765923 5000000000 8906354487587 20000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627722131/5000000000 : ℝ)^549 ≤ (21608971099359/50000000000000 : ℝ)^421 := by
    have hnat : (2627722131 : ℕ)^549*50000000000000^421 ≤ 21608971099359^421*5000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627722131 5000000000 21608971099359 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399738513/2000000000 : ℝ)^549 ≤ (12250285350817/100000000000000 : ℝ)^421 := by
    have hnat : (399738513 : ℕ)^549*100000000000000^421 ≤ 12250285350817^421*2000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399738513 2000000000 12250285350817 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688765923/5000000000 : ℝ), (2627722131/5000000000 : ℝ), (-399738513/2000000000 : ℝ)] ![(8906354487587/20000000000000 : ℝ), (21608971099359/50000000000000 : ℝ), (12250285350817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688765923/5000000000 : ℝ)|^549 ≤ (8906354487587/20000000000000 : ℝ)^421
        have hw : |(2688765923/5000000000 : ℝ)|=(2688765923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627722131/5000000000 : ℝ)|^549 ≤ (21608971099359/50000000000000 : ℝ)^421
        have hw : |(2627722131/5000000000 : ℝ)|=(2627722131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-399738513/2000000000 : ℝ)|^549 ≤ (12250285350817/100000000000000 : ℝ)^421
        have hw : |(-399738513/2000000000 : ℝ)|=(399738513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1432_box_15 (p : ℝ) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4128568843/10000000000 : ℝ)*x 0 + (274660299/625000000 : ℝ)*x 1 + (4394564401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128568843/10000000000 : ℝ)^549 ≤ (31549173517267/100000000000000 : ℝ)^421 := by
    have hnat : (4128568843 : ℕ)^549*100000000000000^421 ≤ 31549173517267^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128568843 10000000000 31549173517267 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274660299/625000000 : ℝ)^549 ≤ (34225415175313/100000000000000 : ℝ)^421 := by
    have hnat : (274660299 : ℕ)^549*100000000000000^421 ≤ 34225415175313^421*625000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274660299 625000000 34225415175313 100000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4394564401/10000000000 : ℝ)^549 ≤ (17112705642781/50000000000000 : ℝ)^421 := by
    have hnat : (4394564401 : ℕ)^549*50000000000000^421 ≤ 17112705642781^421*10000000000^549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394564401 10000000000 17112705642781 50000000000000 549 421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (549/128 : ℝ)) 549 421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128568843/10000000000 : ℝ), (274660299/625000000 : ℝ), (4394564401/10000000000 : ℝ)] ![(31549173517267/100000000000000 : ℝ), (34225415175313/100000000000000 : ℝ), (17112705642781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128568843/10000000000 : ℝ)|^549 ≤ (31549173517267/100000000000000 : ℝ)^421
        have hw : |(4128568843/10000000000 : ℝ)|=(4128568843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274660299/625000000 : ℝ)|^549 ≤ (34225415175313/100000000000000 : ℝ)^421
        have hw : |(274660299/625000000 : ℝ)|=(274660299/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4394564401/10000000000 : ℝ)|^549 ≤ (17112705642781/50000000000000 : ℝ)^421
        have hw : |(4394564401/10000000000 : ℝ)|=(4394564401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1432_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62901/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59119/100000 : ℝ) ∧ (16093/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10587/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11347/100000 : ℝ) ^ (4391/1024 : ℝ) ≤ (885622704854463/10000000000000000000 : ℝ) := by
    have hpowers : (11347/100000 : ℝ)^4391 ≤ (885622704854463/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11347 : ℕ)^4391*10000000000000000000^1024 ≤ 885622704854463^1024*100000^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11347 100000 885622704854463 10000000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11347/100000 : ℝ)) (X := (885622704854463/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7379/50000 : ℝ) ^ (4391/1024 : ℝ) ≤ (3416870718744927/12500000000000000000 : ℝ) := by
    have hpowers : (7379/50000 : ℝ)^4391 ≤ (3416870718744927/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7379 : ℕ)^4391*12500000000000000000^1024 ≤ 3416870718744927^1024*50000^4391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7379 50000 3416870718744927 12500000000000000000 4391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7379/50000 : ℝ)) (X := (3416870718744927/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000885622704854463/5000000000000000000 : ℝ) ≤ (2500103258491333/2500000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (5000885622704854463/5000000000000000000 : ℝ)^1024 ≤ (2500103258491333/2500000000000000 : ℝ)^4391 := by
      have hnat : (5000885622704854463 : ℕ)^1024*2500000000000000^4391 ≤ 2500103258491333^4391*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000885622704854463 5000000000000000000 2500103258491333 2500000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500103258491333/2500000000000000 : ℝ)) (X := (5000885622704854463/5000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018095596399252023/50000000000000000000 : ℝ) ≤ (2500210969256689/2500000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (50018095596399252023/50000000000000000000 : ℝ)^1024 ≤ (2500210969256689/2500000000000000 : ℝ)^4391 := by
      have hnat : (50018095596399252023 : ℕ)^1024*2500000000000000^4391 ≤ 2500210969256689^4391*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018095596399252023 50000000000000000000 2500210969256689 2500000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500210969256689/2500000000000000 : ℝ)) (X := (50018095596399252023/50000000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253416870718744927/6250000000000000000 : ℝ) ≤ (500063736004409/500000000000000 : ℝ) ^ (4391/1024 : ℝ) := by
    have hpowers : (6253416870718744927/6250000000000000000 : ℝ)^1024 ≤ (500063736004409/500000000000000 : ℝ)^4391 := by
      have hnat : (6253416870718744927 : ℕ)^1024*500000000000000^4391 ≤ 500063736004409^4391*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253416870718744927 6250000000000000000 500063736004409 500000000000000 1024 4391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500063736004409/500000000000000 : ℝ)) (X := (6253416870718744927/6250000000000000000 : ℝ)) (by norm_num) 4391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(885622704854463/10000000000000000000 : ℝ) ≤ ((2841802608868315933/2842500000000000000 : ℝ)+2*(8975897113/7106250000000 : ℝ)*(11347/100000 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (2841802608868315933/2842500000000000000 : ℝ)+2*(8975897113/7106250000000 : ℝ)*(11347/100000 : ℝ)=(2500103258491333/2500000000000000 : ℝ) by norm_num, show 1+2*(885622704854463/10000000000000000000 : ℝ)=(5000885622704854463/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3416870718744927/12500000000000000000 : ℝ)+(885622704854463/10000000000000000000 : ℝ) ≤ ((2841802608868315933/2842500000000000000 : ℝ)+(8975897113/7106250000000 : ℝ)*((7379/50000 : ℝ)+(11347/100000 : ℝ)))^(4391/1024 : ℝ) := by
    rw [show (2841802608868315933/2842500000000000000 : ℝ)+(8975897113/7106250000000 : ℝ)*((7379/50000 : ℝ)+(11347/100000 : ℝ))=(2500210969256689/2500000000000000 : ℝ) by norm_num, show 1+(3416870718744927/12500000000000000000 : ℝ)+(885622704854463/10000000000000000000 : ℝ)=(50018095596399252023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3416870718744927/12500000000000000000 : ℝ) ≤ ((2841802608868315933/2842500000000000000 : ℝ)+2*(8975897113/7106250000000 : ℝ)*(7379/50000 : ℝ))^(4391/1024 : ℝ) := by
    rw [show (2841802608868315933/2842500000000000000 : ℝ)+2*(8975897113/7106250000000 : ℝ)*(7379/50000 : ℝ)=(500063736004409/500000000000000 : ℝ) by norm_num, show 1+2*(3416870718744927/12500000000000000000 : ℝ)=(6253416870718744927/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2841802608868315933/2842500000000000000 : ℝ)*(X 1 0+X 2 0)+(8975897113/7106250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (2841802608868315933/2842500000000000000 : ℝ)) (alpha := (8975897113/7106250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2841802608868315933/2842500000000000000 : ℝ)*(X 0 1+X 2 1)+(8975897113/7106250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (2841802608868315933/2842500000000000000 : ℝ)) (alpha := (8975897113/7106250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2841802608868315933/2842500000000000000 : ℝ)*(X 0 2+X 1 2)+(8975897113/7106250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4391/1024 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (2841802608868315933/2842500000000000000 : ℝ)) (alpha := (8975897113/7106250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-226032377/1250000000 : ℝ)*X 0 0+(2693063551/5000000000 : ℝ)*X 0 1+(107722543/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286086501/10000000000 : ℝ)*X 1 0+(-38914257/200000000 : ℝ)*X 1 1+(673265893/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321521617/2500000000 : ℝ)*X 2 0+(2693063567/5000000000 : ℝ)*X 2 1+(-1945712909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2224930211/5000000000 : ℝ)*X 0 0+(4234210331/10000000000 : ℝ)*X 0 1+(4234210357/10000000000 : ℝ)*X 0 2+(2224930211/5000000000 : ℝ)*X 1 0+(4234210331/10000000000 : ℝ)*X 1 1+(4234210357/10000000000 : ℝ)*X 1 2+(2224930211/5000000000 : ℝ)*X 2 0+(4234210331/10000000000 : ℝ)*X 2 1+(4234210357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-213187567/1000000000 : ℝ)*X 0 0+(1316642811/2500000000 : ℝ)*X 0 1+(5266571477/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((335609239/625000000 : ℝ)*X 1 0+(-398854489/2000000000 : ℝ)*X 1 1+(1053314167/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((83902299/156250000 : ℝ)*X 2 0+(5266572111/10000000000 : ℝ)*X 2 1+(-997135831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((519542211/1250000000 : ℝ)*X 0 0+(21904603/50000000 : ℝ)*X 0 1+(1095230303/2500000000 : ℝ)*X 0 2+(519542211/1250000000 : ℝ)*X 1 0+(21904603/50000000 : ℝ)*X 1 1+(1095230303/2500000000 : ℝ)*X 1 2+(519542211/1250000000 : ℝ)*X 2 0+(21904603/50000000 : ℝ)*X 2 1+(1095230303/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-515926489/2500000000 : ℝ)*X 0 0+(5183861527/10000000000 : ℝ)*X 0 1+(5400099367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638152803/5000000000 : ℝ)*X 1 0+(-1939911921/10000000000 : ℝ)*X 1 1+(5400098771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1055261061/2000000000 : ℝ)*X 2 0+(2700049423/5000000000 : ℝ)*X 2 1+(-969956113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4483605877/10000000000 : ℝ)*X 0 0+(1054262521/2500000000 : ℝ)*X 0 1+(4217051021/10000000000 : ℝ)*X 0 2+(4483605877/10000000000 : ℝ)*X 1 0+(1054262521/2500000000 : ℝ)*X 1 1+(4217051021/10000000000 : ℝ)*X 1 2+(4483605877/10000000000 : ℝ)*X 2 0+(1054262521/2500000000 : ℝ)*X 2 1+(4217051021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1876604417/10000000000 : ℝ)*X 0 0+(683352367/1250000000 : ℝ)*X 0 1+(262772177/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1075506403/2000000000 : ℝ)*X 1 0+(-999346191/5000000000 : ℝ)*X 1 1+(1313861057/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2688765923/5000000000 : ℝ)*X 2 0+(2627722131/5000000000 : ℝ)*X 2 1+(-399738513/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4128568843/10000000000 : ℝ)*X 0 0+(274660299/625000000 : ℝ)*X 0 1+(4394564401/10000000000 : ℝ)*X 0 2+(4128568843/10000000000 : ℝ)*X 1 0+(274660299/625000000 : ℝ)*X 1 1+(4394564401/10000000000 : ℝ)*X 1 2+(4128568843/10000000000 : ℝ)*X 2 0+(274660299/625000000 : ℝ)*X 2 1+(4394564401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1432_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62901/100000 : ℝ) ≤ (-14899144165714076825063195619969/23687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14320423/25000000000000 : ℝ)*(lower1) + (75228977/50000000000000 : ℝ)*(lower2) + (11583897/6250000000000 : ℝ)*(lower3) + (87326577/100000000000000 : ℝ)*(lower4) + (1510053361382007/50000000000000 : ℝ)*(major0) + (1510053361382007/50000000000000 : ℝ)*(major1) + (1510053361382007/50000000000000 : ℝ)*(major2) + (11590587737/100000000000000 : ℝ)*(sp1) + (519146123106749/12500000000000 : ℝ)*(sp4) + (259572337141641/6250000000000 : ℝ)*(sp5) + (1038211350132217/25000000000000 : ℝ)*(sp6) + (1907986310833627/100000000000000 : ℝ)*(sp7) + (80896081281/25000000000000 : ℝ)*(sp14) + (12201861777/50000000000000 : ℝ)*(sp15) + (1908010714557181/100000000000000 : ℝ)*(f.failure) + (519146123106749/12500000000000 : ℝ)*(f.sum) + (5681391726847/947500000000000000000000000 : ℝ)*base65 + (148778262035660823/47375000000000000000000000000000 : ℝ)*base68 + (382828993094089177/47375000000000000000000000000000 : ℝ)*base69 + (271175506423785823/47375000000000000000000000000000 : ℝ)*base72 + (2337650575267/947500000000000000000000000 : ℝ)*base73 + (100157020992089177/47375000000000000000000000000000 : ℝ)*base75 + (229094936074910823/47375000000000000000000000000000 : ℝ)*base78 + (201915615367160823/47375000000000000000000000000000 : ℝ)*base80 + (9231041634157/947500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (21937487/10000000000000000000000 : ℝ)*base89 + (21937487/10000000000000000000000 : ℝ)*base91 + (21937487/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59119/100000 : ℝ) ≤ (14004457737477243937813902990031/23687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5752591/100000000000000 : ℝ)*(lower0) + (24693007/100000000000000 : ℝ)*(upper2) + (2992521/100000000000000 : ℝ)*(lower4) + (6006977/100000000000000 : ℝ)*(lower5) + (1545913008850669/50000000000000 : ℝ)*(major0) + (1545913008850669/50000000000000 : ℝ)*(major1) + (1545913008850669/50000000000000 : ℝ)*(major2) + (4210622330207533/100000000000000 : ℝ)*(sp0) + (2105311191587003/50000000000000 : ℝ)*(sp1) + (842124806308487/20000000000000 : ℝ)*(sp2) + (976659796317871/50000000000000 : ℝ)*(sp3) + (1648368429/100000000000000 : ℝ)*(sp5) + (585392383/50000000000000 : ℝ)*(sp7) + (850667451/50000000000000 : ℝ)*(sp12) + (1953320763420509/100000000000000 : ℝ)*(f.failure) + (842124806308487/20000000000000 : ℝ)*(f.sum) + (17651334983423/2842500000000000000000000000 : ℝ)*base66 + (1883401129160790823/142125000000000000000000000000000 : ℝ)*base68 + (1776963215812290823/142125000000000000000000000000000 : ℝ)*base70 + (1211648992883040823/142125000000000000000000000000000 : ℝ)*base72 + (32723838714841/5685000000000000000000000000 : ℝ)*base74 + (1404557775401415823/142125000000000000000000000000000 : ℝ)*base76 + (1694522670968790823/142125000000000000000000000000000 : ℝ)*base78 + (1246505981701290823/142125000000000000000000000000000 : ℝ)*base80 + (16219300273469/5685000000000000000000000000 : ℝ)*base81 + (131724143/10000000000000000000000 : ℝ)*base89 + (131724143/10000000000000000000000 : ℝ)*base91 + (131724143/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (16093/20000 : ℝ) ≤ (38121502896375312652162884556977/47375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18543541/12500000000000 : ℝ)*(upper0) + (87680981/50000000000000 : ℝ)*(upper2) + (16677389/25000000000000 : ℝ)*(lower5) + (3399559199812731/100000000000000 : ℝ)*(major0) + (3399559199812731/100000000000000 : ℝ)*(major1) + (3399559199812731/100000000000000 : ℝ)*(major2) + (9243209153/25000000000000 : ℝ)*(sp1) + (15564173859/50000000000000 : ℝ)*(sp3) + (11583895203/100000000000000 : ℝ)*(sp4) + (924907045074979/20000000000000 : ℝ)*(sp8) + (578065221055289/12500000000000 : ℝ)*(sp9) + (1156139685319731/25000000000000 : ℝ)*(sp10) + (536926503142381/25000000000000 : ℝ)*(sp11) + (477280353/4000000000000 : ℝ)*(sp12) + (2147737140917243/100000000000000 : ℝ)*(f.failure) + (1156139685319731/25000000000000 : ℝ)*(f.sum) + (2051641426439/1895000000000000000000000000 : ℝ)*base66 + (1333286016667664341/94750000000000000000000000000000 : ℝ)*base67 + (489989787456414341/94750000000000000000000000000000 : ℝ)*base69 + (516033805041914341/94750000000000000000000000000000 : ℝ)*base71 + (8586088078513/947500000000000000000000000 : ℝ)*base73 + (289836297947414341/94750000000000000000000000000000 : ℝ)*base75 + (63922998844085659/94750000000000000000000000000000 : ℝ)*base78 + (472260916420585659/94750000000000000000000000000000 : ℝ)*base80 + (1821482527173/947500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (63366361/10000000000000000000000 : ℝ)*base89 + (63366361/10000000000000000000000 : ℝ)*base91 + (63366361/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-10587/12500 : ℝ) ≤ (-320988338929032207829766709/379000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61467477/25000000000000 : ℝ)*(upper3) + (33429023/100000000000000 : ℝ)*(lower4) + (1553773/3125000000000 : ℝ)*(upper5) + (343707414360417/10000000000000 : ℝ)*(major0) + (343707414360417/10000000000000 : ℝ)*(major1) + (343707414360417/10000000000000 : ℝ)*(major2) + (1628201329/25000000000000 : ℝ)*(sp0) + (29883573379/50000000000000 : ℝ)*(sp5) + (19764478657/20000000000000 : ℝ)*(sp7) + (4217440377/100000000000000 : ℝ)*(sp8) + (4730930790585899/100000000000000 : ℝ)*(sp12) + (2365440876842417/50000000000000 : ℝ)*(sp13) + (591367690103949/12500000000000 : ℝ)*(sp14) + (2171339108357161/100000000000000 : ℝ)*(sp15) + (1085718965375223/50000000000000 : ℝ)*(f.failure) + (591367690103949/12500000000000 : ℝ)*(f.sum) + (112102395921/94750000000000000000000000 : ℝ)*base66 + (75273353219149687/9475000000000000000000000000000 : ℝ)*base67 + (38961575449674687/9475000000000000000000000000000 : ℝ)*base69 + (43068944880200313/9475000000000000000000000000000 : ℝ)*base72 + (252884694607/37900000000000000000000000 : ℝ)*base73 + (2155451052250313/9475000000000000000000000000000 : ℝ)*base76 + (32350481221950313/9475000000000000000000000000000 : ℝ)*base78 + (26448756586874687/9475000000000000000000000000000 : ℝ)*base79 + (570077944349/75800000000000000000000000 : ℝ)*base81 + (37180179/5000000000000000000000 : ℝ)*base90 + (37180179/5000000000000000000000 : ℝ)*base92 + (37180179/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1432_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62901/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59119/100000 : ℝ) else (16093/20000 : ℝ) ≤ X j i ∧ X j i ≤ (10587/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1432_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1432_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62901/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59119/100000 : ℝ) else (16093/20000 : ℝ) ≤ X j i ∧ X j i ≤ (10587/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1432_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1432_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1432_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4391/1024 : ℝ) ≤ p) (hpb : p ≤ (549/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158285627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62901/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59119/100000 : ℝ) else (16093/20000 : ℝ) ≤ X j i ∧ X j i ≤ (10587/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1432_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
