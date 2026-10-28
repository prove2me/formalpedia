-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1117_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:02.135305+00:00
-- url     : https://prove2.me/submissions/f66d77eb-31a4-4e4c-b7ca-f57fabd7fcab

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
theorem support_rectangle_w1117_s3_0 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087405649/5000000000 : ℝ)*x 0 + (5431806663/10000000000 : ℝ)*x 1 + (326854869/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087405649/5000000000 : ℝ)^4155 ≤ (6602280138589/50000000000000 : ℝ)^3131 := by
    have hnat : (1087405649 : ℕ)^4155*50000000000000^3131 ≤ 6602280138589^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087405649 5000000000 6602280138589 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431806663/10000000000 : ℝ)^4155 ≤ (44489476131931/100000000000000 : ℝ)^3131 := by
    have hnat : (5431806663 : ℕ)^4155*100000000000000^3131 ≤ 44489476131931^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431806663 10000000000 44489476131931 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326854869/625000000 : ℝ)^4155 ≤ (8461192715043/20000000000000 : ℝ)^3131 := by
    have hnat : (326854869 : ℕ)^4155*20000000000000^3131 ≤ 8461192715043^3131*625000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326854869 625000000 8461192715043 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087405649/5000000000 : ℝ), (5431806663/10000000000 : ℝ), (326854869/625000000 : ℝ)] ![(6602280138589/50000000000000 : ℝ), (44489476131931/100000000000000 : ℝ), (8461192715043/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087405649/5000000000 : ℝ)|^4155 ≤ (6602280138589/50000000000000 : ℝ)^3131
        have hw : |(-1087405649/5000000000 : ℝ)|=(1087405649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431806663/10000000000 : ℝ)|^4155 ≤ (44489476131931/100000000000000 : ℝ)^3131
        have hw : |(5431806663/10000000000 : ℝ)|=(5431806663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326854869/625000000 : ℝ)|^4155 ≤ (8461192715043/20000000000000 : ℝ)^3131
        have hw : |(326854869/625000000 : ℝ)|=(326854869/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s3_1 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070880429/2000000000 : ℝ)*x 0 + (-284773801/1250000000 : ℝ)*x 1 + (81713717/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070880429/2000000000 : ℝ)^4155 ≤ (10912527816343/25000000000000 : ℝ)^3131 := by
    have hnat : (1070880429 : ℕ)^4155*25000000000000^3131 ≤ 10912527816343^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070880429 2000000000 10912527816343 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284773801/1250000000 : ℝ)^4155 ≤ (14043925317251/100000000000000 : ℝ)^3131 := by
    have hnat : (284773801 : ℕ)^4155*100000000000000^3131 ≤ 14043925317251^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284773801 1250000000 14043925317251 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81713717/156250000 : ℝ)^4155 ≤ (846119268069/2000000000000 : ℝ)^3131 := by
    have hnat : (81713717 : ℕ)^4155*2000000000000^3131 ≤ 846119268069^3131*156250000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81713717 156250000 846119268069 2000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070880429/2000000000 : ℝ), (-284773801/1250000000 : ℝ), (81713717/156250000 : ℝ)] ![(10912527816343/25000000000000 : ℝ), (14043925317251/100000000000000 : ℝ), (846119268069/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070880429/2000000000 : ℝ)|^4155 ≤ (10912527816343/25000000000000 : ℝ)^3131
        have hw : |(1070880429/2000000000 : ℝ)|=(1070880429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284773801/1250000000 : ℝ)|^4155 ≤ (14043925317251/100000000000000 : ℝ)^3131
        have hw : |(-284773801/1250000000 : ℝ)|=(284773801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81713717/156250000 : ℝ)|^4155 ≤ (846119268069/2000000000000 : ℝ)^3131
        have hw : |(81713717/156250000 : ℝ)|=(81713717/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s3_2 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354402257/10000000000 : ℝ)*x 0 + (522967799/1000000000 : ℝ)*x 1 + (-18225521/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354402257/10000000000 : ℝ)^4155 ≤ (43650112477031/100000000000000 : ℝ)^3131 := by
    have hnat : (5354402257 : ℕ)^4155*100000000000000^3131 ≤ 43650112477031^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354402257 10000000000 43650112477031 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522967799/1000000000 : ℝ)^4155 ≤ (42305964498451/100000000000000 : ℝ)^3131 := by
    have hnat : (522967799 : ℕ)^4155*100000000000000^3131 ≤ 42305964498451^3131*1000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522967799 1000000000 42305964498451 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18225521/80000000 : ℝ)^4155 ≤ (2808784600427/20000000000000 : ℝ)^3131 := by
    have hnat : (18225521 : ℕ)^4155*20000000000000^3131 ≤ 2808784600427^3131*80000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18225521 80000000 2808784600427 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354402257/10000000000 : ℝ), (522967799/1000000000 : ℝ), (-18225521/80000000 : ℝ)] ![(43650112477031/100000000000000 : ℝ), (42305964498451/100000000000000 : ℝ), (2808784600427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354402257/10000000000 : ℝ)|^4155 ≤ (43650112477031/100000000000000 : ℝ)^3131
        have hw : |(5354402257/10000000000 : ℝ)|=(5354402257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522967799/1000000000 : ℝ)|^4155 ≤ (42305964498451/100000000000000 : ℝ)^3131
        have hw : |(522967799/1000000000 : ℝ)|=(522967799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18225521/80000000 : ℝ)|^4155 ≤ (2808784600427/20000000000000 : ℝ)^3131
        have hw : |(-18225521/80000000 : ℝ)|=(18225521/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s3_3 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2182891901/5000000000 : ℝ)*x 0 + (4170286951/10000000000 : ℝ)*x 1 + (571305659/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182891901/5000000000 : ℝ)^4155 ≤ (33292302685043/100000000000000 : ℝ)^3131 := by
    have hnat : (2182891901 : ℕ)^4155*100000000000000^3131 ≤ 33292302685043^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182891901 5000000000 33292302685043 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170286951/10000000000 : ℝ)^4155 ≤ (31328559554107/100000000000000 : ℝ)^3131 := by
    have hnat : (4170286951 : ℕ)^4155*100000000000000^3131 ≤ 31328559554107^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170286951 10000000000 31328559554107 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571305659/1250000000 : ℝ)^4155 ≤ (17689568869833/50000000000000 : ℝ)^3131 := by
    have hnat : (571305659 : ℕ)^4155*50000000000000^3131 ≤ 17689568869833^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571305659 1250000000 17689568869833 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182891901/5000000000 : ℝ), (4170286951/10000000000 : ℝ), (571305659/1250000000 : ℝ)] ![(33292302685043/100000000000000 : ℝ), (31328559554107/100000000000000 : ℝ), (17689568869833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182891901/5000000000 : ℝ)|^4155 ≤ (33292302685043/100000000000000 : ℝ)^3131
        have hw : |(2182891901/5000000000 : ℝ)|=(2182891901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170286951/10000000000 : ℝ)|^4155 ≤ (31328559554107/100000000000000 : ℝ)^3131
        have hw : |(4170286951/10000000000 : ℝ)|=(4170286951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571305659/1250000000 : ℝ)|^4155 ≤ (17689568869833/50000000000000 : ℝ)^3131
        have hw : |(571305659/1250000000 : ℝ)|=(571305659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s3_4 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2174830587/10000000000 : ℝ)*x 0 + (5230476253/10000000000 : ℝ)*x 1 + (678875477/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174830587/10000000000 : ℝ)^4155 ≤ (6602357847473/50000000000000 : ℝ)^3131 := by
    have hnat : (2174830587 : ℕ)^4155*50000000000000^3131 ≤ 6602357847473^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174830587 10000000000 6602357847473 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230476253/10000000000 : ℝ)^4155 ≤ (1057863357839/2500000000000 : ℝ)^3131 := by
    have hnat : (5230476253 : ℕ)^4155*2500000000000^3131 ≤ 1057863357839^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230476253 10000000000 1057863357839 2500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678875477/1250000000 : ℝ)^4155 ≤ (44480749970551/100000000000000 : ℝ)^3131 := by
    have hnat : (678875477 : ℕ)^4155*100000000000000^3131 ≤ 44480749970551^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678875477 1250000000 44480749970551 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2174830587/10000000000 : ℝ), (5230476253/10000000000 : ℝ), (678875477/1250000000 : ℝ)] ![(6602357847473/50000000000000 : ℝ), (1057863357839/2500000000000 : ℝ), (44480749970551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2174830587/10000000000 : ℝ)|^4155 ≤ (6602357847473/50000000000000 : ℝ)^3131
        have hw : |(-2174830587/10000000000 : ℝ)|=(2174830587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230476253/10000000000 : ℝ)|^4155 ≤ (1057863357839/2500000000000 : ℝ)^3131
        have hw : |(5230476253/10000000000 : ℝ)|=(5230476253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678875477/1250000000 : ℝ)|^4155 ≤ (44480749970551/100000000000000 : ℝ)^3131
        have hw : |(678875477/1250000000 : ℝ)|=(678875477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s3_5 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651644071/5000000000 : ℝ)*x 0 + (-51921609/250000000 : ℝ)*x 1 + (1357750989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651644071/5000000000 : ℝ)^4155 ≤ (21549002751241/50000000000000 : ℝ)^3131 := by
    have hnat : (2651644071 : ℕ)^4155*50000000000000^3131 ≤ 21549002751241^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651644071 5000000000 21549002751241 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51921609/250000000 : ℝ)^4155 ≤ (2426024021/19531250000 : ℝ)^3131 := by
    have hnat : (51921609 : ℕ)^4155*19531250000^3131 ≤ 2426024021^3131*250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51921609 250000000 2426024021 19531250000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357750989/2500000000 : ℝ)^4155 ≤ (44480751492177/100000000000000 : ℝ)^3131 := by
    have hnat : (1357750989 : ℕ)^4155*100000000000000^3131 ≤ 44480751492177^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357750989 2500000000 44480751492177 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651644071/5000000000 : ℝ), (-51921609/250000000 : ℝ), (1357750989/2500000000 : ℝ)] ![(21549002751241/50000000000000 : ℝ), (2426024021/19531250000 : ℝ), (44480751492177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651644071/5000000000 : ℝ)|^4155 ≤ (21549002751241/50000000000000 : ℝ)^3131
        have hw : |(2651644071/5000000000 : ℝ)|=(2651644071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51921609/250000000 : ℝ)|^4155 ≤ (2426024021/19531250000 : ℝ)^3131
        have hw : |(-51921609/250000000 : ℝ)|=(51921609/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357750989/2500000000 : ℝ)|^4155 ≤ (44480751492177/100000000000000 : ℝ)^3131
        have hw : |(1357750989/2500000000 : ℝ)|=(1357750989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s3_6 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662911019/1250000000 : ℝ)*x 0 + (2715501917/5000000000 : ℝ)*x 1 + (-415372903/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662911019/1250000000 : ℝ)^4155 ≤ (43098005610327/100000000000000 : ℝ)^3131 := by
    have hnat : (662911019 : ℕ)^4155*100000000000000^3131 ≤ 43098005610327^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662911019 1250000000 43098005610327 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715501917/5000000000 : ℝ)^4155 ≤ (44480750166189/100000000000000 : ℝ)^3131 := by
    have hnat : (2715501917 : ℕ)^4155*100000000000000^3131 ≤ 44480750166189^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715501917 5000000000 44480750166189 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415372903/2000000000 : ℝ)^4155 ≤ (12421244217723/100000000000000 : ℝ)^3131 := by
    have hnat : (415372903 : ℕ)^4155*100000000000000^3131 ≤ 12421244217723^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415372903 2000000000 12421244217723 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662911019/1250000000 : ℝ), (2715501917/5000000000 : ℝ), (-415372903/2000000000 : ℝ)] ![(43098005610327/100000000000000 : ℝ), (44480750166189/100000000000000 : ℝ), (12421244217723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662911019/1250000000 : ℝ)|^4155 ≤ (43098005610327/100000000000000 : ℝ)^3131
        have hw : |(662911019/1250000000 : ℝ)|=(662911019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715501917/5000000000 : ℝ)|^4155 ≤ (44480750166189/100000000000000 : ℝ)^3131
        have hw : |(2715501917/5000000000 : ℝ)|=(2715501917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-415372903/2000000000 : ℝ)|^4155 ≤ (12421244217723/100000000000000 : ℝ)^3131
        have hw : |(-415372903/2000000000 : ℝ)|=(415372903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s3_7 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4365821983/10000000000 : ℝ)*x 0 + (4568865361/10000000000 : ℝ)*x 1 + (2085937987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365821983/10000000000 : ℝ)^4155 ≤ (1664634453379/5000000000000 : ℝ)^3131 := by
    have hnat : (4365821983 : ℕ)^4155*5000000000000^3131 ≤ 1664634453379^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365821983 10000000000 1664634453379 5000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4568865361/10000000000 : ℝ)^4155 ≤ (3536290900117/10000000000000 : ℝ)^3131 := by
    have hnat : (4568865361 : ℕ)^4155*10000000000000^3131 ≤ 3536290900117^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4568865361 10000000000 3536290900117 10000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085937987/5000000000 : ℝ)^4155 ≤ (31344401907219/100000000000000 : ℝ)^3131 := by
    have hnat : (2085937987 : ℕ)^4155*100000000000000^3131 ≤ 31344401907219^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085937987 5000000000 31344401907219 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365821983/10000000000 : ℝ), (4568865361/10000000000 : ℝ), (2085937987/5000000000 : ℝ)] ![(1664634453379/5000000000000 : ℝ), (3536290900117/10000000000000 : ℝ), (31344401907219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365821983/10000000000 : ℝ)|^4155 ≤ (1664634453379/5000000000000 : ℝ)^3131
        have hw : |(4365821983/10000000000 : ℝ)|=(4365821983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4568865361/10000000000 : ℝ)|^4155 ≤ (3536290900117/10000000000000 : ℝ)^3131
        have hw : |(4568865361/10000000000 : ℝ)|=(4568865361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085937987/5000000000 : ℝ)|^4155 ≤ (31344401907219/100000000000000 : ℝ)^3131
        have hw : |(2085937987/5000000000 : ℝ)|=(2085937987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1117_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8289/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2239/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10559/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3709/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8289/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2239/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8289/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2239/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8289/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2239/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8289/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2239/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8289/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2239/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8289/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2239/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2239/25000 : ℝ) ^ (8309/2048 : ℝ) ≤ (224208335613649/4000000000000000000 : ℝ) := by
    have hpowers : (2239/25000 : ℝ)^8309 ≤ (224208335613649/4000000000000000000 : ℝ)^2048 := by
      have hnat : (2239 : ℕ)^8309*4000000000000000000^2048 ≤ 224208335613649^2048*25000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2239 25000 224208335613649 4000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2239/25000 : ℝ)) (X := (224208335613649/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8289/50000 : ℝ) ^ (8309/2048 : ℝ) ≤ (34080916877869891/50000000000000000000 : ℝ) := by
    have hpowers : (8289/50000 : ℝ)^8309 ≤ (34080916877869891/50000000000000000000 : ℝ)^2048 := by
      have hnat : (8289 : ℕ)^8309*50000000000000000000^2048 ≤ 34080916877869891^2048*50000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8289 50000 34080916877869891 50000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8289/50000 : ℝ)) (X := (34080916877869891/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000224208335613649/2000000000000000000 : ℝ) ≤ (5000138151185029/5000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (2000224208335613649/2000000000000000000 : ℝ)^2048 ≤ (5000138151185029/5000000000000000 : ℝ)^8309 := by
      have hnat : (2000224208335613649 : ℕ)^2048*5000000000000000^8309 ≤ 5000138151185029^8309*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000224208335613649 2000000000000000000 5000138151185029 5000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000138151185029/5000000000000000 : ℝ)) (X := (2000224208335613649/2000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100073767042146081007/100000000000000000000 : ℝ) ≤ (10001817702887787/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (100073767042146081007/100000000000000000000 : ℝ)^2048 ≤ (10001817702887787/10000000000000000 : ℝ)^8309 := by
      have hnat : (100073767042146081007 : ℕ)^2048*10000000000000000^8309 ≤ 10001817702887787^8309*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100073767042146081007 100000000000000000000 10001817702887787 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001817702887787/10000000000000000 : ℝ)) (X := (100073767042146081007/100000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25034080916877869891/25000000000000000000 : ℝ) ≤ (2500839775851379/2500000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (25034080916877869891/25000000000000000000 : ℝ)^2048 ≤ (2500839775851379/2500000000000000 : ℝ)^8309 := by
      have hnat : (25034080916877869891 : ℕ)^2048*2500000000000000^8309 ≤ 2500839775851379^8309*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25034080916877869891 25000000000000000000 2500839775851379 2500000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500839775851379/2500000000000000 : ℝ)) (X := (25034080916877869891/25000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(224208335613649/4000000000000000000 : ℝ) ≤ ((19048624102647755057/19055000000000000000 : ℝ)+2*(1541400517729/762200000000000 : ℝ)*(2239/25000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (19048624102647755057/19055000000000000000 : ℝ)+2*(1541400517729/762200000000000 : ℝ)*(2239/25000 : ℝ)=(5000138151185029/5000000000000000 : ℝ) by norm_num, show 1+2*(224208335613649/4000000000000000000 : ℝ)=(2000224208335613649/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34080916877869891/50000000000000000000 : ℝ)+(224208335613649/4000000000000000000 : ℝ) ≤ ((19048624102647755057/19055000000000000000 : ℝ)+(1541400517729/762200000000000 : ℝ)*((8289/50000 : ℝ)+(2239/25000 : ℝ)))^(8309/2048 : ℝ) := by
    rw [show (19048624102647755057/19055000000000000000 : ℝ)+(1541400517729/762200000000000 : ℝ)*((8289/50000 : ℝ)+(2239/25000 : ℝ))=(10001817702887787/10000000000000000 : ℝ) by norm_num, show 1+(34080916877869891/50000000000000000000 : ℝ)+(224208335613649/4000000000000000000 : ℝ)=(100073767042146081007/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34080916877869891/50000000000000000000 : ℝ) ≤ ((19048624102647755057/19055000000000000000 : ℝ)+2*(1541400517729/762200000000000 : ℝ)*(8289/50000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (19048624102647755057/19055000000000000000 : ℝ)+2*(1541400517729/762200000000000 : ℝ)*(8289/50000 : ℝ)=(2500839775851379/2500000000000000 : ℝ) by norm_num, show 1+2*(34080916877869891/50000000000000000000 : ℝ)=(25034080916877869891/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19048624102647755057/19055000000000000000 : ℝ)*(X 1 0+X 2 0)+(1541400517729/762200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (2239/25000 : ℝ)) (hi := (8289/50000 : ℝ)) (c := (19048624102647755057/19055000000000000000 : ℝ)) (alpha := (1541400517729/762200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19048624102647755057/19055000000000000000 : ℝ)*(X 0 1+X 2 1)+(1541400517729/762200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (2239/25000 : ℝ)) (hi := (8289/50000 : ℝ)) (c := (19048624102647755057/19055000000000000000 : ℝ)) (alpha := (1541400517729/762200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19048624102647755057/19055000000000000000 : ℝ)*(X 0 2+X 1 2)+(1541400517729/762200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (2239/25000 : ℝ)) (hi := (8289/50000 : ℝ)) (c := (19048624102647755057/19055000000000000000 : ℝ)) (alpha := (1541400517729/762200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1087405649/5000000000 : ℝ)*X 0 0+(5431806663/10000000000 : ℝ)*X 0 1+(326854869/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070880429/2000000000 : ℝ)*X 1 0+(-284773801/1250000000 : ℝ)*X 1 1+(81713717/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354402257/10000000000 : ℝ)*X 2 0+(522967799/1000000000 : ℝ)*X 2 1+(-18225521/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182891901/5000000000 : ℝ)*X 0 0+(4170286951/10000000000 : ℝ)*X 0 1+(571305659/1250000000 : ℝ)*X 0 2+(2182891901/5000000000 : ℝ)*X 1 0+(4170286951/10000000000 : ℝ)*X 1 1+(571305659/1250000000 : ℝ)*X 1 2+(2182891901/5000000000 : ℝ)*X 2 0+(4170286951/10000000000 : ℝ)*X 2 1+(571305659/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2174830587/10000000000 : ℝ)*X 0 0+(5230476253/10000000000 : ℝ)*X 0 1+(678875477/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651644071/5000000000 : ℝ)*X 1 0+(-51921609/250000000 : ℝ)*X 1 1+(1357750989/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662911019/1250000000 : ℝ)*X 2 0+(2715501917/5000000000 : ℝ)*X 2 1+(-415372903/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365821983/10000000000 : ℝ)*X 0 0+(4568865361/10000000000 : ℝ)*X 0 1+(2085937987/5000000000 : ℝ)*X 0 2+(4365821983/10000000000 : ℝ)*X 1 0+(4568865361/10000000000 : ℝ)*X 1 1+(2085937987/5000000000 : ℝ)*X 1 2+(4365821983/10000000000 : ℝ)*X 2 0+(4568865361/10000000000 : ℝ)*X 2 1+(2085937987/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2134155266033650824837119277/238187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (455170781/20000000000000 : ℝ)*(base19) + (534822131/25000000000000 : ℝ)*(base23) + (32133437/25000000000000 : ℝ)*(lower2) + (148077361/100000000000000 : ℝ)*(upper3) + (3435217/1250000000000 : ℝ)*(upper5) + (930809564711487/25000000000000 : ℝ)*(major0) + (930809564711487/25000000000000 : ℝ)*(major1) + (930809564711487/25000000000000 : ℝ)*(major2) + (2473690162850311/50000000000000 : ℝ)*(sp0) + (247371211341629/5000000000000 : ℝ)*(sp1) + (123685609084949/2500000000000 : ℝ)*(sp2) + (624757611851821/25000000000000 : ℝ)*(sp3) + (46176985863/100000000000000 : ℝ)*(sp4) + (19268932109/100000000000000 : ℝ)*(sp7) + (39047651817803/1562500000000 : ℝ)*(f.failure) + (1236856625671621/25000000000000 : ℝ)*(f.sum) + (85966373123/148867187500000000000000000 : ℝ)*base66 + (5231849432116435241/476375000000000000000000000000000 : ℝ)*base68 + (7939344252350435241/476375000000000000000000000000000 : ℝ)*base70 + (3457956056119810241/476375000000000000000000000000000 : ℝ)*base72 + (78837358074569/19055000000000000000000000000 : ℝ)*base74 + (1406903852126564759/476375000000000000000000000000000 : ℝ)*base75 + (9319898879097310241/476375000000000000000000000000000 : ℝ)*base78 + (7743726810830439759/476375000000000000000000000000000 : ℝ)*base79 + (7956361389431/4763750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (753957/78125000000000000000 : ℝ)*base90 + (753957/78125000000000000000 : ℝ)*base92 + (753957/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (296622518944389992538792843/95275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (572077467/100000000000000 : ℝ)*(base19) + (373791021/50000000000000 : ℝ)*(base23) + (22328337/25000000000000 : ℝ)*(upper3) + (42595009/50000000000000 : ℝ)*(lower4) + (27031663/100000000000000 : ℝ)*(upper5) + (375290075273233/10000000000000 : ℝ)*(major0) + (375290075273233/10000000000000 : ℝ)*(major1) + (375290075273233/10000000000000 : ℝ)*(major2) + (1501819991/12500000000000 : ℝ)*(sp1) + (3145389067/25000000000000 : ℝ)*(sp2) + (4986842122279323/100000000000000 : ℝ)*(sp4) + (623353691955241/12500000000000 : ℝ)*(sp5) + (4986828793141013/100000000000000 : ℝ)*(sp6) + (125947963970383/5000000000000 : ℝ)*(sp7) + (125947963970383/5000000000000 : ℝ)*(f.failure) + (4986842122279323/100000000000000 : ℝ)*(f.sum) + (93919055333/59546875000000000000000000 : ℝ)*base66 + (2041866583430464281/190550000000000000000000000000000 : ℝ)*base67 + (1672672324565485719/190550000000000000000000000000000 : ℝ)*base70 + (404637476724885719/190550000000000000000000000000000 : ℝ)*base72 + (857857359059/3811000000000000000000000000 : ℝ)*base74 + (81397404190685719/190550000000000000000000000000000 : ℝ)*base76 + (66451531098685719/190550000000000000000000000000000 : ℝ)*base78 + (2417751526616814281/190550000000000000000000000000000 : ℝ)*base79 + (7000702996619/1905500000000000000000000000 : ℝ)*base82 + (2579977/250000000000000000000 : ℝ)*base90 + (2579977/250000000000000000000 : ℝ)*base92 + (2579977/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1117_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8289/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2239/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10559/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3709/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1117_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1117_s4_0 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089012173/5000000000 : ℝ)*x 0 + (2701558531/5000000000 : ℝ)*x 1 + (5256266231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089012173/5000000000 : ℝ)^4155 ≤ (1323045506827/10000000000000 : ℝ)^3131 := by
    have hnat : (1089012173 : ℕ)^4155*10000000000000^3131 ≤ 1323045506827^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089012173 5000000000 1323045506827 10000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701558531/5000000000 : ℝ)^4155 ≤ (44177910356511/100000000000000 : ℝ)^3131 := by
    have hnat : (2701558531 : ℕ)^4155*100000000000000^3131 ≤ 44177910356511^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701558531 5000000000 44177910356511 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256266231/10000000000 : ℝ)^4155 ≤ (42591634557101/100000000000000 : ℝ)^3131 := by
    have hnat : (5256266231 : ℕ)^4155*100000000000000^3131 ≤ 42591634557101^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256266231 10000000000 42591634557101 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089012173/5000000000 : ℝ), (2701558531/5000000000 : ℝ), (5256266231/10000000000 : ℝ)] ![(1323045506827/10000000000000 : ℝ), (44177910356511/100000000000000 : ℝ), (42591634557101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089012173/5000000000 : ℝ)|^4155 ≤ (1323045506827/10000000000000 : ℝ)^3131
        have hw : |(-1089012173/5000000000 : ℝ)|=(1089012173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701558531/5000000000 : ℝ)|^4155 ≤ (44177910356511/100000000000000 : ℝ)^3131
        have hw : |(2701558531/5000000000 : ℝ)|=(2701558531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256266231/10000000000 : ℝ)|^4155 ≤ (42591634557101/100000000000000 : ℝ)^3131
        have hw : |(5256266231/10000000000 : ℝ)|=(5256266231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s4_1 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20887717/39062500 : ℝ)*x 0 + (-563167951/2500000000 : ℝ)*x 1 + (5256266353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20887717/39062500 : ℝ)^4155 ≤ (43572813569009/100000000000000 : ℝ)^3131 := by
    have hnat : (20887717 : ℕ)^4155*100000000000000^3131 ≤ 43572813569009^3131*39062500^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20887717 39062500 43572813569009 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563167951/2500000000 : ℝ)^4155 ≤ (13835550549951/100000000000000 : ℝ)^3131 := by
    have hnat : (563167951 : ℕ)^4155*100000000000000^3131 ≤ 13835550549951^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563167951 2500000000 13835550549951 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256266353/10000000000 : ℝ)^4155 ≤ (42591635868983/100000000000000 : ℝ)^3131 := by
    have hnat : (5256266353 : ℕ)^4155*100000000000000^3131 ≤ 42591635868983^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256266353 10000000000 42591635868983 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20887717/39062500 : ℝ), (-563167951/2500000000 : ℝ), (5256266353/10000000000 : ℝ)] ![(43572813569009/100000000000000 : ℝ), (13835550549951/100000000000000 : ℝ), (42591635868983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20887717/39062500 : ℝ)|^4155 ≤ (43572813569009/100000000000000 : ℝ)^3131
        have hw : |(20887717/39062500 : ℝ)|=(20887717/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-563167951/2500000000 : ℝ)|^4155 ≤ (13835550549951/100000000000000 : ℝ)^3131
        have hw : |(-563167951/2500000000 : ℝ)|=(563167951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256266353/10000000000 : ℝ)|^4155 ≤ (42591635868983/100000000000000 : ℝ)^3131
        have hw : |(5256266353/10000000000 : ℝ)|=(5256266353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s4_2 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347255357/10000000000 : ℝ)*x 0 + (657033263/1250000000 : ℝ)*x 1 + (-2252672391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347255357/10000000000 : ℝ)^4155 ≤ (21786405730173/50000000000000 : ℝ)^3131 := by
    have hnat : (5347255357 : ℕ)^4155*50000000000000^3131 ≤ 21786405730173^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347255357 10000000000 21786405730173 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657033263/1250000000 : ℝ)^4155 ≤ (21295816595727/50000000000000 : ℝ)^3131 := by
    have hnat : (657033263 : ℕ)^4155*50000000000000^3131 ≤ 21295816595727^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657033263 1250000000 21295816595727 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252672391/10000000000 : ℝ)^4155 ≤ (13835555334319/100000000000000 : ℝ)^3131 := by
    have hnat : (2252672391 : ℕ)^4155*100000000000000^3131 ≤ 13835555334319^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252672391 10000000000 13835555334319 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347255357/10000000000 : ℝ), (657033263/1250000000 : ℝ), (-2252672391/10000000000 : ℝ)] ![(21786405730173/50000000000000 : ℝ), (21295816595727/50000000000000 : ℝ), (13835555334319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347255357/10000000000 : ℝ)|^4155 ≤ (21786405730173/50000000000000 : ℝ)^3131
        have hw : |(5347255357/10000000000 : ℝ)|=(5347255357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657033263/1250000000 : ℝ)|^4155 ≤ (21295816595727/50000000000000 : ℝ)^3131
        have hw : |(657033263/1250000000 : ℝ)|=(657033263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2252672391/10000000000 : ℝ)|^4155 ≤ (13835555334319/100000000000000 : ℝ)^3131
        have hw : |(-2252672391/10000000000 : ℝ)|=(2252672391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s4_3 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545962111/1250000000 : ℝ)*x 0 + (1056188703/2500000000 : ℝ)*x 1 + (2257739837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545962111/1250000000 : ℝ)^4155 ≤ (16655832007347/50000000000000 : ℝ)^3131 := by
    have hnat : (545962111 : ℕ)^4155*50000000000000^3131 ≤ 16655832007347^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545962111 1250000000 16655832007347 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056188703/2500000000 : ℝ)^4155 ≤ (3984089949861/12500000000000 : ℝ)^3131 := by
    have hnat : (1056188703 : ℕ)^4155*12500000000000^3131 ≤ 3984089949861^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056188703 2500000000 3984089949861 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257739837/5000000000 : ℝ)^4155 ≤ (34815616359907/100000000000000 : ℝ)^3131 := by
    have hnat : (2257739837 : ℕ)^4155*100000000000000^3131 ≤ 34815616359907^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257739837 5000000000 34815616359907 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545962111/1250000000 : ℝ), (1056188703/2500000000 : ℝ), (2257739837/5000000000 : ℝ)] ![(16655832007347/50000000000000 : ℝ), (3984089949861/12500000000000 : ℝ), (34815616359907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545962111/1250000000 : ℝ)|^4155 ≤ (16655832007347/50000000000000 : ℝ)^3131
        have hw : |(545962111/1250000000 : ℝ)|=(545962111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056188703/2500000000 : ℝ)|^4155 ≤ (3984089949861/12500000000000 : ℝ)^3131
        have hw : |(1056188703/2500000000 : ℝ)|=(1056188703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257739837/5000000000 : ℝ)|^4155 ≤ (34815616359907/100000000000000 : ℝ)^3131
        have hw : |(2257739837/5000000000 : ℝ)|=(2257739837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s4_4 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-435606329/2000000000 : ℝ)*x 0 + (2628344141/5000000000 : ℝ)*x 1 + (1080538673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435606329/2000000000 : ℝ)^4155 ≤ (3307628476761/25000000000000 : ℝ)^3131 := by
    have hnat : (435606329 : ℕ)^4155*25000000000000^3131 ≤ 3307628476761^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435606329 2000000000 3307628476761 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628344141/5000000000 : ℝ)^4155 ≤ (42596172986143/100000000000000 : ℝ)^3131 := by
    have hnat : (2628344141 : ℕ)^4155*100000000000000^3131 ≤ 42596172986143^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628344141 5000000000 42596172986143 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080538673/2000000000 : ℝ)^4155 ≤ (44173313101731/100000000000000 : ℝ)^3131 := by
    have hnat : (1080538673 : ℕ)^4155*100000000000000^3131 ≤ 44173313101731^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080538673 2000000000 44173313101731 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435606329/2000000000 : ℝ), (2628344141/5000000000 : ℝ), (1080538673/2000000000 : ℝ)] ![(3307628476761/25000000000000 : ℝ), (42596172986143/100000000000000 : ℝ), (44173313101731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435606329/2000000000 : ℝ)|^4155 ≤ (3307628476761/25000000000000 : ℝ)^3131
        have hw : |(-435606329/2000000000 : ℝ)|=(435606329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628344141/5000000000 : ℝ)|^4155 ≤ (42596172986143/100000000000000 : ℝ)^3131
        have hw : |(2628344141/5000000000 : ℝ)|=(2628344141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080538673/2000000000 : ℝ)|^4155 ≤ (44173313101731/100000000000000 : ℝ)^3131
        have hw : |(1080538673/2000000000 : ℝ)|=(1080538673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s4_5 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310121471/10000000000 : ℝ)*x 0 + (-2106245241/10000000000 : ℝ)*x 1 + (2701346739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310121471/10000000000 : ℝ)^4155 ≤ (172686860177/400000000000 : ℝ)^3131 := by
    have hnat : (5310121471 : ℕ)^4155*400000000000^3131 ≤ 172686860177^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310121471 10000000000 172686860177 400000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106245241/10000000000 : ℝ)^4155 ≤ (12654970618123/100000000000000 : ℝ)^3131 := by
    have hnat : (2106245241 : ℕ)^4155*100000000000000^3131 ≤ 12654970618123^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106245241 10000000000 12654970618123 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701346739/5000000000 : ℝ)^4155 ≤ (44173314327803/100000000000000 : ℝ)^3131 := by
    have hnat : (2701346739 : ℕ)^4155*100000000000000^3131 ≤ 44173314327803^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701346739 5000000000 44173314327803 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310121471/10000000000 : ℝ), (-2106245241/10000000000 : ℝ), (2701346739/5000000000 : ℝ)] ![(172686860177/400000000000 : ℝ), (12654970618123/100000000000000 : ℝ), (44173314327803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310121471/10000000000 : ℝ)|^4155 ≤ (172686860177/400000000000 : ℝ)^3131
        have hw : |(5310121471/10000000000 : ℝ)|=(5310121471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2106245241/10000000000 : ℝ)|^4155 ≤ (12654970618123/100000000000000 : ℝ)^3131
        have hw : |(-2106245241/10000000000 : ℝ)|=(2106245241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701346739/5000000000 : ℝ)|^4155 ≤ (44173314327803/100000000000000 : ℝ)^3131
        have hw : |(2701346739/5000000000 : ℝ)|=(2701346739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s4_6 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310121591/10000000000 : ℝ)*x 0 + (2701346763/5000000000 : ℝ)*x 1 + (-2106245013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310121591/10000000000 : ℝ)^4155 ≤ (8634343267787/20000000000000 : ℝ)^3131 := by
    have hnat : (5310121591 : ℕ)^4155*20000000000000^3131 ≤ 8634343267787^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310121591 10000000000 8634343267787 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701346763/5000000000 : ℝ)^4155 ≤ (44173314848613/100000000000000 : ℝ)^3131 := by
    have hnat : (2701346763 : ℕ)^4155*100000000000000^3131 ≤ 44173314848613^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701346763 5000000000 44173314848613 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106245013/10000000000 : ℝ)^4155 ≤ (6327484400101/50000000000000 : ℝ)^3131 := by
    have hnat : (2106245013 : ℕ)^4155*50000000000000^3131 ≤ 6327484400101^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106245013 10000000000 6327484400101 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310121591/10000000000 : ℝ), (2701346763/5000000000 : ℝ), (-2106245013/10000000000 : ℝ)] ![(8634343267787/20000000000000 : ℝ), (44173314848613/100000000000000 : ℝ), (6327484400101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310121591/10000000000 : ℝ)|^4155 ≤ (8634343267787/20000000000000 : ℝ)^3131
        have hw : |(5310121591/10000000000 : ℝ)|=(5310121591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701346763/5000000000 : ℝ)|^4155 ≤ (44173314848613/100000000000000 : ℝ)^3131
        have hw : |(2701346763/5000000000 : ℝ)|=(2701346763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106245013/10000000000 : ℝ)|^4155 ≤ (6327484400101/50000000000000 : ℝ)^3131
        have hw : |(-2106245013/10000000000 : ℝ)|=(2106245013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s4_7 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4367712143/10000000000 : ℝ)*x 0 + (282165227/625000000 : ℝ)*x 1 + (4225593777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367712143/10000000000 : ℝ)^4155 ≤ (33311818413613/100000000000000 : ℝ)^3131 := by
    have hnat : (4367712143 : ℕ)^4155*100000000000000^3131 ≤ 33311818413613^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367712143 10000000000 33311818413613 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282165227/625000000 : ℝ)^4155 ≤ (34807062283943/100000000000000 : ℝ)^3131 := by
    have hnat : (282165227 : ℕ)^4155*100000000000000^3131 ≤ 34807062283943^3131*625000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282165227 625000000 34807062283943 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225593777/10000000000 : ℝ)^4155 ≤ (15940559646963/50000000000000 : ℝ)^3131 := by
    have hnat : (4225593777 : ℕ)^4155*50000000000000^3131 ≤ 15940559646963^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225593777 10000000000 15940559646963 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367712143/10000000000 : ℝ), (282165227/625000000 : ℝ), (4225593777/10000000000 : ℝ)] ![(33311818413613/100000000000000 : ℝ), (34807062283943/100000000000000 : ℝ), (15940559646963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367712143/10000000000 : ℝ)|^4155 ≤ (33311818413613/100000000000000 : ℝ)^3131
        have hw : |(4367712143/10000000000 : ℝ)|=(4367712143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282165227/625000000 : ℝ)|^4155 ≤ (34807062283943/100000000000000 : ℝ)^3131
        have hw : |(282165227/625000000 : ℝ)|=(282165227/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225593777/10000000000 : ℝ)|^4155 ≤ (15940559646963/50000000000000 : ℝ)^3131
        have hw : |(4225593777/10000000000 : ℝ)|=(4225593777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1117_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3709/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10559/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11127/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3709/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10559/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3709/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10559/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3709/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10559/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3709/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10559/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3709/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10559/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3709/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10559/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10559/100000 : ℝ) ^ (8309/2048 : ℝ) ≤ (1366538307054211/12500000000000000000 : ℝ) := by
    have hpowers : (10559/100000 : ℝ)^8309 ≤ (1366538307054211/12500000000000000000 : ℝ)^2048 := by
      have hnat : (10559 : ℕ)^8309*12500000000000000000^2048 ≤ 1366538307054211^2048*100000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10559 100000 1366538307054211 12500000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10559/100000 : ℝ)) (X := (1366538307054211/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3709/25000 : ℝ) ^ (8309/2048 : ℝ) ≤ (1357611652368567/3125000000000000000 : ℝ) := by
    have hpowers : (3709/25000 : ℝ)^8309 ≤ (1357611652368567/3125000000000000000 : ℝ)^2048 := by
      have hnat : (3709 : ℕ)^8309*3125000000000000000^2048 ≤ 1357611652368567^2048*25000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3709 25000 1357611652368567 3125000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3709/25000 : ℝ)) (X := (1357611652368567/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251366538307054211/6250000000000000000 : ℝ) ≤ (10000538873979699/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (6251366538307054211/6250000000000000000 : ℝ)^2048 ≤ (10000538873979699/10000000000000000 : ℝ)^8309 := by
      have hnat : (6251366538307054211 : ℕ)^2048*10000000000000000^8309 ≤ 10000538873979699^8309*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251366538307054211 6250000000000000000 10000538873979699 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538873979699/10000000000000000 : ℝ)) (X := (6251366538307054211/6250000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506796984916528479/12500000000000000000 : ℝ) ≤ (1000133998066919/1000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (12506796984916528479/12500000000000000000 : ℝ)^2048 ≤ (1000133998066919/1000000000000000 : ℝ)^8309 := by
      have hnat : (12506796984916528479 : ℕ)^2048*1000000000000000^8309 ≤ 1000133998066919^8309*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506796984916528479 12500000000000000000 1000133998066919 1000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000133998066919/1000000000000000 : ℝ)) (X := (12506796984916528479/12500000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563857611652368567/1562500000000000000 : ℝ) ≤ (10002141087358681/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (1563857611652368567/1562500000000000000 : ℝ)^2048 ≤ (10002141087358681/10000000000000000 : ℝ)^8309 := by
      have hnat : (1563857611652368567 : ℕ)^2048*10000000000000000^8309 ≤ 10002141087358681^8309*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563857611652368567 1562500000000000000 10002141087358681 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002141087358681/10000000000000000 : ℝ)) (X := (1563857611652368567/1562500000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1366538307054211/12500000000000000000 : ℝ) ≤ ((8551077398588500337/8554000000000000000 : ℝ)+2*(801106689491/427700000000000 : ℝ)*(10559/100000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (8551077398588500337/8554000000000000000 : ℝ)+2*(801106689491/427700000000000 : ℝ)*(10559/100000 : ℝ)=(10000538873979699/10000000000000000 : ℝ) by norm_num, show 1+2*(1366538307054211/12500000000000000000 : ℝ)=(6251366538307054211/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1357611652368567/3125000000000000000 : ℝ)+(1366538307054211/12500000000000000000 : ℝ) ≤ ((8551077398588500337/8554000000000000000 : ℝ)+(801106689491/427700000000000 : ℝ)*((3709/25000 : ℝ)+(10559/100000 : ℝ)))^(8309/2048 : ℝ) := by
    rw [show (8551077398588500337/8554000000000000000 : ℝ)+(801106689491/427700000000000 : ℝ)*((3709/25000 : ℝ)+(10559/100000 : ℝ))=(1000133998066919/1000000000000000 : ℝ) by norm_num, show 1+(1357611652368567/3125000000000000000 : ℝ)+(1366538307054211/12500000000000000000 : ℝ)=(12506796984916528479/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1357611652368567/3125000000000000000 : ℝ) ≤ ((8551077398588500337/8554000000000000000 : ℝ)+2*(801106689491/427700000000000 : ℝ)*(3709/25000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (8551077398588500337/8554000000000000000 : ℝ)+2*(801106689491/427700000000000 : ℝ)*(3709/25000 : ℝ)=(10002141087358681/10000000000000000 : ℝ) by norm_num, show 1+2*(1357611652368567/3125000000000000000 : ℝ)=(1563857611652368567/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8551077398588500337/8554000000000000000 : ℝ)*(X 1 0+X 2 0)+(801106689491/427700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (10559/100000 : ℝ)) (hi := (3709/25000 : ℝ)) (c := (8551077398588500337/8554000000000000000 : ℝ)) (alpha := (801106689491/427700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8551077398588500337/8554000000000000000 : ℝ)*(X 0 1+X 2 1)+(801106689491/427700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (10559/100000 : ℝ)) (hi := (3709/25000 : ℝ)) (c := (8551077398588500337/8554000000000000000 : ℝ)) (alpha := (801106689491/427700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8551077398588500337/8554000000000000000 : ℝ)*(X 0 2+X 1 2)+(801106689491/427700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (10559/100000 : ℝ)) (hi := (3709/25000 : ℝ)) (c := (8551077398588500337/8554000000000000000 : ℝ)) (alpha := (801106689491/427700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1089012173/5000000000 : ℝ)*X 0 0+(2701558531/5000000000 : ℝ)*X 0 1+(5256266231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((20887717/39062500 : ℝ)*X 1 0+(-563167951/2500000000 : ℝ)*X 1 1+(5256266353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347255357/10000000000 : ℝ)*X 2 0+(657033263/1250000000 : ℝ)*X 2 1+(-2252672391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545962111/1250000000 : ℝ)*X 0 0+(1056188703/2500000000 : ℝ)*X 0 1+(2257739837/5000000000 : ℝ)*X 0 2+(545962111/1250000000 : ℝ)*X 1 0+(1056188703/2500000000 : ℝ)*X 1 1+(2257739837/5000000000 : ℝ)*X 1 2+(545962111/1250000000 : ℝ)*X 2 0+(1056188703/2500000000 : ℝ)*X 2 1+(2257739837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-435606329/2000000000 : ℝ)*X 0 0+(2628344141/5000000000 : ℝ)*X 0 1+(1080538673/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310121471/10000000000 : ℝ)*X 1 0+(-2106245241/10000000000 : ℝ)*X 1 1+(2701346739/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310121591/10000000000 : ℝ)*X 2 0+(2701346763/5000000000 : ℝ)*X 2 1+(-2106245013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367712143/10000000000 : ℝ)*X 0 0+(282165227/625000000 : ℝ)*X 0 1+(4225593777/10000000000 : ℝ)*X 0 2+(4367712143/10000000000 : ℝ)*X 1 0+(282165227/625000000 : ℝ)*X 1 1+(4225593777/10000000000 : ℝ)*X 1 2+(4367712143/10000000000 : ℝ)*X 2 0+(282165227/625000000 : ℝ)*X 2 1+(4225593777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94577043789463655183247/21385000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1591707823/100000000000000 : ℝ)*(base19) + (1490664063/100000000000000 : ℝ)*(base23) + (15610239/12500000000000 : ℝ)*(upper2) + (17305741/5000000000000 : ℝ)*(upper3) + (5124726284215541/100000000000000 : ℝ)*(major0) + (5124726284215541/100000000000000 : ℝ)*(major1) + (5124726284215541/100000000000000 : ℝ)*(major2) + (6809685748680697/100000000000000 : ℝ)*(sp0) + (1361943551836867/20000000000000 : ℝ)*(sp1) + (136194108788637/2000000000000 : ℝ)*(sp2) + (3439703787888157/100000000000000 : ℝ)*(sp3) + (16801105731/50000000000000 : ℝ)*(sp4) + (3105199061/25000000000000 : ℝ)*(sp6) + (29282231161/100000000000000 : ℝ)*(sp7) + (1719866535059659/50000000000000 : ℝ)*(f.failure) + (3404859675446079/50000000000000 : ℝ)*(f.sum) + (28058812553/41767578125000000000000000 : ℝ)*base65 + (3021758511811842683/855400000000000000000000000000000 : ℝ)*base68 + (1423597428129042683/855400000000000000000000000000000 : ℝ)*base70 + (859822797236842683/855400000000000000000000000000000 : ℝ)*base72 + (76778050423671/21385000000000000000000000000 : ℝ)*base73 + (6045594883433757317/855400000000000000000000000000000 : ℝ)*base75 + (1445611306499557317/855400000000000000000000000000000 : ℝ)*base77 + (10780387162559757317/855400000000000000000000000000000 : ℝ)*base79 + (30144911704837/10692500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (7280621/2500000000000000000000 : ℝ)*base90 + (7280621/2500000000000000000000 : ℝ)*base92 + (7280621/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (862109161743510336576683019/85540000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (323049213/20000000000000 : ℝ)*(base19) + (2293090583/100000000000000 : ℝ)*(base23) + (22496043/6250000000000 : ℝ)*(upper3) + (6054733/3125000000000 : ℝ)*(lower4) + (78380163/25000000000000 : ℝ)*(upper5) + (1030868415397757/20000000000000 : ℝ)*(major0) + (1030868415397757/20000000000000 : ℝ)*(major1) + (1030868415397757/20000000000000 : ℝ)*(major2) + (31417400191/100000000000000 : ℝ)*(sp1) + (27019748497/50000000000000 : ℝ)*(sp2) + (6849072530782327/100000000000000 : ℝ)*(sp4) + (6849039498136071/100000000000000 : ℝ)*(sp5) + (6849016198194751/100000000000000 : ℝ)*(sp6) + (1729805643623729/50000000000000 : ℝ)*(sp7) + (1729805643623729/50000000000000 : ℝ)*(f.failure) + (6849072530782327/100000000000000 : ℝ)*(f.sum) + (3200721163413/534625000000000000000000000 : ℝ)*base65 + (2043974661473684109/171080000000000000000000000000000 : ℝ)*base67 + (1013294724288604109/171080000000000000000000000000000 : ℝ)*base69 + (4131990031790924109/171080000000000000000000000000000 : ℝ)*base71 + (117804612733/85540000000000000000000000 : ℝ)*base74 + (962799092622124109/171080000000000000000000000000000 : ℝ)*base75 + (1149625130558844109/171080000000000000000000000000000 : ℝ)*base77 + (631986207830644109/171080000000000000000000000000000 : ℝ)*base79 + (5026646689157/2138500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (47080951/2500000000000000000000 : ℝ)*base90 + (47080951/2500000000000000000000 : ℝ)*base92 + (47080951/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1117_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3709/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10559/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1117_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1117_s5_0 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-27233937/125000000 : ℝ)*x 0 + (13488951/25000000 : ℝ)*x 1 + (5263350071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27233937/125000000 : ℝ)^4155 ≤ (264720450771/2000000000000 : ℝ)^3131 := by
    have hnat : (27233937 : ℕ)^4155*2000000000000^3131 ≤ 264720450771^3131*125000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27233937 125000000 264720450771 2000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13488951/25000000 : ℝ)^4155 ≤ (8819230530457/20000000000000 : ℝ)^3131 := by
    have hnat : (13488951 : ℕ)^4155*20000000000000^3131 ≤ 8819230530457^3131*25000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13488951 25000000 8819230530457 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263350071/10000000000 : ℝ)^4155 ≤ (42667824794867/100000000000000 : ℝ)^3131 := by
    have hnat : (5263350071 : ℕ)^4155*100000000000000^3131 ≤ 42667824794867^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263350071 10000000000 42667824794867 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27233937/125000000 : ℝ), (13488951/25000000 : ℝ), (5263350071/10000000000 : ℝ)] ![(264720450771/2000000000000 : ℝ), (8819230530457/20000000000000 : ℝ), (42667824794867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27233937/125000000 : ℝ)|^4155 ≤ (264720450771/2000000000000 : ℝ)^3131
        have hw : |(-27233937/125000000 : ℝ)|=(27233937/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13488951/25000000 : ℝ)|^4155 ≤ (8819230530457/20000000000000 : ℝ)^3131
        have hw : |(13488951/25000000 : ℝ)|=(13488951/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263350071/10000000000 : ℝ)|^4155 ≤ (42667824794867/100000000000000 : ℝ)^3131
        have hw : |(5263350071/10000000000 : ℝ)|=(5263350071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s5_1 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167042827/312500000 : ℝ)*x 0 + (-2245821557/10000000000 : ℝ)*x 1 + (2631675037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167042827/312500000 : ℝ)^4155 ≤ (43552430047587/100000000000000 : ℝ)^3131 := by
    have hnat : (167042827 : ℕ)^4155*100000000000000^3131 ≤ 43552430047587^3131*312500000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167042827 312500000 43552430047587 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245821557/10000000000 : ℝ)^4155 ≤ (13779745108293/100000000000000 : ℝ)^3131 := by
    have hnat : (2245821557 : ℕ)^4155*100000000000000^3131 ≤ 13779745108293^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245821557 10000000000 13779745108293 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631675037/5000000000 : ℝ)^4155 ≤ (42667824827141/100000000000000 : ℝ)^3131 := by
    have hnat : (2631675037 : ℕ)^4155*100000000000000^3131 ≤ 42667824827141^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631675037 5000000000 42667824827141 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167042827/312500000 : ℝ), (-2245821557/10000000000 : ℝ), (2631675037/5000000000 : ℝ)] ![(43552430047587/100000000000000 : ℝ), (13779745108293/100000000000000 : ℝ), (42667824827141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167042827/312500000 : ℝ)|^4155 ≤ (43552430047587/100000000000000 : ℝ)^3131
        have hw : |(167042827/312500000 : ℝ)|=(167042827/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2245821557/10000000000 : ℝ)|^4155 ≤ (13779745108293/100000000000000 : ℝ)^3131
        have hw : |(-2245821557/10000000000 : ℝ)|=(2245821557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631675037/5000000000 : ℝ)|^4155 ≤ (42667824827141/100000000000000 : ℝ)^3131
        have hw : |(2631675037/5000000000 : ℝ)|=(2631675037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s5_2 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345370483/10000000000 : ℝ)*x 0 + (5263350061/10000000000 : ℝ)*x 1 + (-2245821549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345370483/10000000000 : ℝ)^4155 ≤ (43552430253023/100000000000000 : ℝ)^3131 := by
    have hnat : (5345370483 : ℕ)^4155*100000000000000^3131 ≤ 43552430253023^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345370483 10000000000 43552430253023 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263350061/10000000000 : ℝ)^4155 ≤ (42667824687289/100000000000000 : ℝ)^3131 := by
    have hnat : (5263350061 : ℕ)^4155*100000000000000^3131 ≤ 42667824687289^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263350061 10000000000 42667824687289 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245821549/10000000000 : ℝ)^4155 ≤ (13779745043153/100000000000000 : ℝ)^3131 := by
    have hnat : (2245821549 : ℕ)^4155*100000000000000^3131 ≤ 13779745043153^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245821549 10000000000 13779745043153 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345370483/10000000000 : ℝ), (5263350061/10000000000 : ℝ), (-2245821549/10000000000 : ℝ)] ![(43552430253023/100000000000000 : ℝ), (42667824687289/100000000000000 : ℝ), (13779745043153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345370483/10000000000 : ℝ)|^4155 ≤ (43552430253023/100000000000000 : ℝ)^3131
        have hw : |(5345370483/10000000000 : ℝ)|=(5345370483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263350061/10000000000 : ℝ)|^4155 ≤ (42667824687289/100000000000000 : ℝ)^3131
        have hw : |(5263350061/10000000000 : ℝ)|=(5263350061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2245821549/10000000000 : ℝ)|^4155 ≤ (13779745043153/100000000000000 : ℝ)^3131
        have hw : |(-2245821549/10000000000 : ℝ)|=(2245821549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s5_3 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2184050861/5000000000 : ℝ)*x 0 + (4239174767/10000000000 : ℝ)*x 1 + (4500954211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184050861/5000000000 : ℝ)^4155 ≤ (6663152296139/20000000000000 : ℝ)^3131 := by
    have hnat : (2184050861 : ℕ)^4155*20000000000000^3131 ≤ 6663152296139^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184050861 5000000000 6663152296139 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239174767/10000000000 : ℝ)^4155 ≤ (4002145953727/12500000000000 : ℝ)^3131 := by
    have hnat : (4239174767 : ℕ)^4155*12500000000000^3131 ≤ 4002145953727^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239174767 10000000000 4002145953727 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500954211/10000000000 : ℝ)^4155 ≤ (34667070872571/100000000000000 : ℝ)^3131 := by
    have hnat : (4500954211 : ℕ)^4155*100000000000000^3131 ≤ 34667070872571^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500954211 10000000000 34667070872571 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184050861/5000000000 : ℝ), (4239174767/10000000000 : ℝ), (4500954211/10000000000 : ℝ)] ![(6663152296139/20000000000000 : ℝ), (4002145953727/12500000000000 : ℝ), (34667070872571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184050861/5000000000 : ℝ)|^4155 ≤ (6663152296139/20000000000000 : ℝ)^3131
        have hw : |(2184050861/5000000000 : ℝ)|=(2184050861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239174767/10000000000 : ℝ)|^4155 ≤ (4002145953727/12500000000000 : ℝ)^3131
        have hw : |(4239174767/10000000000 : ℝ)|=(4239174767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500954211/10000000000 : ℝ)|^4155 ≤ (34667070872571/100000000000000 : ℝ)^3131
        have hw : |(4500954211/10000000000 : ℝ)|=(4500954211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s5_4 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089360159/5000000000 : ℝ)*x 0 + (210547701/400000000 : ℝ)*x 1 + (5395236723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089360159/5000000000 : ℝ)^4155 ≤ (13236065734987/100000000000000 : ℝ)^3131 := by
    have hnat : (1089360159 : ℕ)^4155*100000000000000^3131 ≤ 13236065734987^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089360159 5000000000 13236065734987 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210547701/400000000 : ℝ)^4155 ≤ (42671508908959/100000000000000 : ℝ)^3131 := by
    have hnat : (210547701 : ℕ)^4155*100000000000000^3131 ≤ 42671508908959^3131*400000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210547701 400000000 42671508908959 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395236723/10000000000 : ℝ)^4155 ≤ (11023106333593/25000000000000 : ℝ)^3131 := by
    have hnat : (5395236723 : ℕ)^4155*25000000000000^3131 ≤ 11023106333593^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395236723 10000000000 11023106333593 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089360159/5000000000 : ℝ), (210547701/400000000 : ℝ), (5395236723/10000000000 : ℝ)] ![(13236065734987/100000000000000 : ℝ), (42671508908959/100000000000000 : ℝ), (11023106333593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089360159/5000000000 : ℝ)|^4155 ≤ (13236065734987/100000000000000 : ℝ)^3131
        have hw : |(-1089360159/5000000000 : ℝ)|=(1089360159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210547701/400000000 : ℝ)|^4155 ≤ (42671508908959/100000000000000 : ℝ)^3131
        have hw : |(210547701/400000000 : ℝ)|=(210547701/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395236723/10000000000 : ℝ)|^4155 ≤ (11023106333593/25000000000000 : ℝ)^3131
        have hw : |(5395236723/10000000000 : ℝ)|=(5395236723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s5_5 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311932507/10000000000 : ℝ)*x 0 + (-528483727/2500000000 : ℝ)*x 1 + (1348809173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311932507/10000000000 : ℝ)^4155 ≤ (4319125547389/10000000000000 : ℝ)^3131 := by
    have hnat : (5311932507 : ℕ)^4155*10000000000000^3131 ≤ 4319125547389^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311932507 10000000000 4319125547389 10000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528483727/2500000000 : ℝ)^4155 ≤ (12716319505261/100000000000000 : ℝ)^3131 := by
    have hnat : (528483727 : ℕ)^4155*100000000000000^3131 ≤ 12716319505261^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528483727 2500000000 12716319505261 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348809173/2500000000 : ℝ)^4155 ≤ (5511553124771/12500000000000 : ℝ)^3131 := by
    have hnat : (1348809173 : ℕ)^4155*12500000000000^3131 ≤ 5511553124771^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348809173 2500000000 5511553124771 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311932507/10000000000 : ℝ), (-528483727/2500000000 : ℝ), (1348809173/2500000000 : ℝ)] ![(4319125547389/10000000000000 : ℝ), (12716319505261/100000000000000 : ℝ), (5511553124771/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311932507/10000000000 : ℝ)|^4155 ≤ (4319125547389/10000000000000 : ℝ)^3131
        have hw : |(5311932507/10000000000 : ℝ)|=(5311932507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528483727/2500000000 : ℝ)|^4155 ≤ (12716319505261/100000000000000 : ℝ)^3131
        have hw : |(-528483727/2500000000 : ℝ)|=(528483727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348809173/2500000000 : ℝ)|^4155 ≤ (5511553124771/12500000000000 : ℝ)^3131
        have hw : |(1348809173/2500000000 : ℝ)|=(1348809173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s5_6 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311932453/10000000000 : ℝ)*x 0 + (5395236723/10000000000 : ℝ)*x 1 + (-105696747/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311932453/10000000000 : ℝ)^4155 ≤ (43191254891217/100000000000000 : ℝ)^3131 := by
    have hnat : (5311932453 : ℕ)^4155*100000000000000^3131 ≤ 43191254891217^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311932453 10000000000 43191254891217 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395236723/10000000000 : ℝ)^4155 ≤ (11023106333593/25000000000000 : ℝ)^3131 := by
    have hnat : (5395236723 : ℕ)^4155*25000000000000^3131 ≤ 11023106333593^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395236723 10000000000 11023106333593 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105696747/500000000 : ℝ)^4155 ≤ (1589539970089/12500000000000 : ℝ)^3131 := by
    have hnat : (105696747 : ℕ)^4155*12500000000000^3131 ≤ 1589539970089^3131*500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105696747 500000000 1589539970089 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311932453/10000000000 : ℝ), (5395236723/10000000000 : ℝ), (-105696747/500000000 : ℝ)] ![(43191254891217/100000000000000 : ℝ), (11023106333593/25000000000000 : ℝ), (1589539970089/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311932453/10000000000 : ℝ)|^4155 ≤ (43191254891217/100000000000000 : ℝ)^3131
        have hw : |(5311932453/10000000000 : ℝ)|=(5311932453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395236723/10000000000 : ℝ)|^4155 ≤ (11023106333593/25000000000000 : ℝ)^3131
        have hw : |(5395236723/10000000000 : ℝ)|=(5395236723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105696747/500000000 : ℝ)|^4155 ≤ (1589539970089/12500000000000 : ℝ)^3131
        have hw : |(-105696747/500000000 : ℝ)|=(105696747/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s5_7 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092028087/2500000000 : ℝ)*x 0 + (4500276377/10000000000 : ℝ)*x 1 + (4239855251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092028087/2500000000 : ℝ)^4155 ≤ (33315869031817/100000000000000 : ℝ)^3131 := by
    have hnat : (1092028087 : ℕ)^4155*100000000000000^3131 ≤ 33315869031817^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092028087 2500000000 33315869031817 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500276377/10000000000 : ℝ)^4155 ≤ (34660142788207/100000000000000 : ℝ)^3131 := by
    have hnat : (4500276377 : ℕ)^4155*100000000000000^3131 ≤ 34660142788207^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500276377 10000000000 34660142788207 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239855251/10000000000 : ℝ)^4155 ≤ (16011994085743/50000000000000 : ℝ)^3131 := by
    have hnat : (4239855251 : ℕ)^4155*50000000000000^3131 ≤ 16011994085743^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239855251 10000000000 16011994085743 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092028087/2500000000 : ℝ), (4500276377/10000000000 : ℝ), (4239855251/10000000000 : ℝ)] ![(33315869031817/100000000000000 : ℝ), (34660142788207/100000000000000 : ℝ), (16011994085743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092028087/2500000000 : ℝ)|^4155 ≤ (33315869031817/100000000000000 : ℝ)^3131
        have hw : |(1092028087/2500000000 : ℝ)|=(1092028087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500276377/10000000000 : ℝ)|^4155 ≤ (34660142788207/100000000000000 : ℝ)^3131
        have hw : |(4500276377/10000000000 : ℝ)|=(4500276377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239855251/10000000000 : ℝ)|^4155 ≤ (16011994085743/50000000000000 : ℝ)^3131
        have hw : |(4239855251/10000000000 : ℝ)|=(4239855251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1117_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5639/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14079/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11127/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11127/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11127/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11127/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11127/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11127/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11127/100000 : ℝ) ^ (8309/2048 : ℝ) ≤ (13521752281161483/100000000000000000000 : ℝ) := by
    have hpowers : (11127/100000 : ℝ)^8309 ≤ (13521752281161483/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11127 : ℕ)^8309*100000000000000000000^2048 ≤ 13521752281161483^2048*100000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11127 100000 13521752281161483 100000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11127/100000 : ℝ)) (X := (13521752281161483/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (8309/2048 : ℝ) ≤ (36754427646932817/100000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^8309 ≤ (36754427646932817/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14237 : ℕ)^8309*100000000000000000000^2048 ≤ 36754427646932817^2048*100000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 36754427646932817 100000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (36754427646932817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013521752281161483/50000000000000000000 : ℝ) ≤ (10000666499640093/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (50013521752281161483/50000000000000000000 : ℝ)^2048 ≤ (10000666499640093/10000000000000000 : ℝ)^8309 := by
      have hnat : (50013521752281161483 : ℕ)^2048*10000000000000000^8309 ≤ 10000666499640093^8309*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013521752281161483 50000000000000000000 10000666499640093 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000666499640093/10000000000000000 : ℝ)) (X := (50013521752281161483/50000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000502761799280943/1000000000000000000 : ℝ) ≤ (2500309742804227/2500000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (1000502761799280943/1000000000000000000 : ℝ)^2048 ≤ (2500309742804227/2500000000000000 : ℝ)^8309 := by
      have hnat : (1000502761799280943 : ℕ)^2048*2500000000000000^8309 ≤ 2500309742804227^8309*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000502761799280943 1000000000000000000 2500309742804227 2500000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500309742804227/2500000000000000 : ℝ)) (X := (1000502761799280943/1000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036754427646932817/50000000000000000000 : ℝ) ≤ (10001811442793723/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (50036754427646932817/50000000000000000000 : ℝ)^2048 ≤ (10001811442793723/10000000000000000 : ℝ)^8309 := by
      have hnat : (50036754427646932817 : ℕ)^2048*10000000000000000^8309 ≤ 10001811442793723^8309*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036754427646932817 50000000000000000000 10001811442793723 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001811442793723/10000000000000000 : ℝ)) (X := (50036754427646932817/50000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13521752281161483/100000000000000000000 : ℝ) ≤ ((1554466651570512411/1555000000000000000 : ℝ)+2*(114494315363/62200000000000 : ℝ)*(11127/100000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (1554466651570512411/1555000000000000000 : ℝ)+2*(114494315363/62200000000000 : ℝ)*(11127/100000 : ℝ)=(10000666499640093/10000000000000000 : ℝ) by norm_num, show 1+2*(13521752281161483/100000000000000000000 : ℝ)=(50013521752281161483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36754427646932817/100000000000000000000 : ℝ)+(13521752281161483/100000000000000000000 : ℝ) ≤ ((1554466651570512411/1555000000000000000 : ℝ)+(114494315363/62200000000000 : ℝ)*((14237/100000 : ℝ)+(11127/100000 : ℝ)))^(8309/2048 : ℝ) := by
    rw [show (1554466651570512411/1555000000000000000 : ℝ)+(114494315363/62200000000000 : ℝ)*((14237/100000 : ℝ)+(11127/100000 : ℝ))=(2500309742804227/2500000000000000 : ℝ) by norm_num, show 1+(36754427646932817/100000000000000000000 : ℝ)+(13521752281161483/100000000000000000000 : ℝ)=(1000502761799280943/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36754427646932817/100000000000000000000 : ℝ) ≤ ((1554466651570512411/1555000000000000000 : ℝ)+2*(114494315363/62200000000000 : ℝ)*(14237/100000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (1554466651570512411/1555000000000000000 : ℝ)+2*(114494315363/62200000000000 : ℝ)*(14237/100000 : ℝ)=(10001811442793723/10000000000000000 : ℝ) by norm_num, show 1+2*(36754427646932817/100000000000000000000 : ℝ)=(50036754427646932817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1554466651570512411/1555000000000000000 : ℝ)*(X 1 0+X 2 0)+(114494315363/62200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (11127/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1554466651570512411/1555000000000000000 : ℝ)) (alpha := (114494315363/62200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1554466651570512411/1555000000000000000 : ℝ)*(X 0 1+X 2 1)+(114494315363/62200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (11127/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1554466651570512411/1555000000000000000 : ℝ)) (alpha := (114494315363/62200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1554466651570512411/1555000000000000000 : ℝ)*(X 0 2+X 1 2)+(114494315363/62200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (11127/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1554466651570512411/1555000000000000000 : ℝ)) (alpha := (114494315363/62200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-27233937/125000000 : ℝ)*X 0 0+(13488951/25000000 : ℝ)*X 0 1+(5263350071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167042827/312500000 : ℝ)*X 1 0+(-2245821557/10000000000 : ℝ)*X 1 1+(2631675037/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345370483/10000000000 : ℝ)*X 2 0+(5263350061/10000000000 : ℝ)*X 2 1+(-2245821549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184050861/5000000000 : ℝ)*X 0 0+(4239174767/10000000000 : ℝ)*X 0 1+(4500954211/10000000000 : ℝ)*X 0 2+(2184050861/5000000000 : ℝ)*X 1 0+(4239174767/10000000000 : ℝ)*X 1 1+(4500954211/10000000000 : ℝ)*X 1 2+(2184050861/5000000000 : ℝ)*X 2 0+(4239174767/10000000000 : ℝ)*X 2 1+(4500954211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1089360159/5000000000 : ℝ)*X 0 0+(210547701/400000000 : ℝ)*X 0 1+(5395236723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311932507/10000000000 : ℝ)*X 1 0+(-528483727/2500000000 : ℝ)*X 1 1+(1348809173/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311932453/10000000000 : ℝ)*X 2 0+(5395236723/10000000000 : ℝ)*X 2 1+(-105696747/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092028087/2500000000 : ℝ)*X 0 0+(4500276377/10000000000 : ℝ)*X 0 1+(4239855251/10000000000 : ℝ)*X 0 2+(1092028087/2500000000 : ℝ)*X 1 0+(4500276377/10000000000 : ℝ)*X 1 1+(4239855251/10000000000 : ℝ)*X 1 2+(1092028087/2500000000 : ℝ)*X 2 0+(4500276377/10000000000 : ℝ)*X 2 1+(4239855251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7136739415451942090605407/1214843750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1191899847/100000000000000 : ℝ)*(base19) + (114816883/10000000000000 : ℝ)*(base23) + (37744837/100000000000000 : ℝ)*(lower2) + (702977/500000000000 : ℝ)*(upper3) + (105479439/100000000000000 : ℝ)*(upper5) + (711416803760441/12500000000000 : ℝ)*(major0) + (711416803760441/12500000000000 : ℝ)*(major1) + (711416803760441/12500000000000 : ℝ)*(major2) + (1512518806461811/20000000000000 : ℝ)*(sp0) + (1512525031732439/20000000000000 : ℝ)*(sp1) + (7562625202393211/100000000000000 : ℝ)*(sp2) + (3820025334853331/100000000000000 : ℝ)*(sp3) + (32318252987/100000000000000 : ℝ)*(sp4) + (4244732793/25000000000000 : ℝ)*(sp7) + (3820042313784503/100000000000000 : ℝ)*(f.failure) + (7562626350562041/100000000000000 : ℝ)*(f.sum) + (37727380251/12148437500000000000000000 : ℝ)*base66 + (512338152352591749/19437500000000000000000000000000 : ℝ)*base68 + (30900018087154249/19437500000000000000000000000000 : ℝ)*base70 + (175241159242716749/19437500000000000000000000000000 : ℝ)*base72 + (2545864259749/777500000000000000000000000 : ℝ)*base74 + (345772316484904249/19437500000000000000000000000000 : ℝ)*base76 + (16556769715845751/19437500000000000000000000000000 : ℝ)*base77 + (159187772193591749/19437500000000000000000000000000 : ℝ)*base80 + (912198417619/777500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1476257/5000000000000000000000 : ℝ)*base90 + (1476257/5000000000000000000000 : ℝ)*base92 + (1476257/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (394780065200007939164147229/38875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (840214821/50000000000000 : ℝ)*(base19) + (87844251/5000000000000 : ℝ)*(base23) + (31931253/20000000000000 : ℝ)*(upper3) + (75964043/100000000000000 : ℝ)*(lower4) + (156390293/100000000000000 : ℝ)*(upper5) + (2860484544813471/50000000000000 : ℝ)*(major0) + (2860484544813471/50000000000000 : ℝ)*(major1) + (2860484544813471/50000000000000 : ℝ)*(major2) + (11194759657/25000000000000 : ℝ)*(sp1) + (23241696647/50000000000000 : ℝ)*(sp2) + (3801002323199741/50000000000000 : ℝ)*(sp4) + (1900489546732803/25000000000000 : ℝ)*(sp5) + (475122275382573/6250000000000 : ℝ)*(sp6) + (959983298587647/25000000000000 : ℝ)*(sp7) + (959983298587647/25000000000000 : ℝ)*(f.failure) + (3801002323199741/50000000000000 : ℝ)*(f.sum) + (3079188438833/1555000000000000000000000000 : ℝ)*base65 + (190557758436686419/77750000000000000000000000000000 : ℝ)*base68 + (1081890238743686419/77750000000000000000000000000000 : ℝ)*base70 + (593817523615186419/77750000000000000000000000000000 : ℝ)*base72 + (3410369172853/1555000000000000000000000000 : ℝ)*base73 + (1173675022641186419/77750000000000000000000000000000 : ℝ)*base76 + (403735429997686419/77750000000000000000000000000000 : ℝ)*base78 + (616306755743686419/77750000000000000000000000000000 : ℝ)*base80 + (8451946822563/1555000000000000000000000000 : ℝ)*base81 + (1429593/1250000000000000000000 : ℝ)*base90 + (1429593/1250000000000000000000 : ℝ)*base92 + (1429593/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1117_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5639/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1117_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1117_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8289/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2239/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5639/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1117_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1117_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1117_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8289/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2239/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5639/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1117_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
