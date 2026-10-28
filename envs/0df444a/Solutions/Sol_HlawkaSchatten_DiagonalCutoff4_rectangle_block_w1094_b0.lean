-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1094_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:59.664314+00:00
-- url     : https://prove2.me/submissions/0a24eb77-bb2c-4bed-81e9-7b61ea5a3966

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
theorem support_rectangle_w1094_s0_0 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1907096263/10000000000 : ℝ)*x 0 + (606549077/1000000000 : ℝ)*x 1 + (4774371753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1907096263/10000000000 : ℝ)^8287 ≤ (86484721473/781250000000 : ℝ)^6239 := by
    have hnat : (1907096263 : ℕ)^8287*781250000000^6239 ≤ 86484721473^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907096263 10000000000 86484721473 781250000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (606549077/1000000000 : ℝ)^8287 ≤ (2573712418807/5000000000000 : ℝ)^6239 := by
    have hnat : (606549077 : ℕ)^8287*5000000000000^6239 ≤ 2573712418807^6239*1000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606549077 1000000000 2573712418807 5000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4774371753/10000000000 : ℝ)^8287 ≤ (7491141451201/20000000000000 : ℝ)^6239 := by
    have hnat : (4774371753 : ℕ)^8287*20000000000000^6239 ≤ 7491141451201^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774371753 10000000000 7491141451201 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1907096263/10000000000 : ℝ), (606549077/1000000000 : ℝ), (4774371753/10000000000 : ℝ)] ![(86484721473/781250000000 : ℝ), (2573712418807/5000000000000 : ℝ), (7491141451201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1907096263/10000000000 : ℝ)|^8287 ≤ (86484721473/781250000000 : ℝ)^6239
        have hw : |(-1907096263/10000000000 : ℝ)|=(1907096263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(606549077/1000000000 : ℝ)|^8287 ≤ (2573712418807/5000000000000 : ℝ)^6239
        have hw : |(606549077/1000000000 : ℝ)|=(606549077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4774371753/10000000000 : ℝ)|^8287 ≤ (7491141451201/20000000000000 : ℝ)^6239
        have hw : |(4774371753/10000000000 : ℝ)|=(4774371753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s0_1 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689937107/1250000000 : ℝ)*x 0 + (-132472287/500000000 : ℝ)*x 1 + (2387185947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689937107/1250000000 : ℝ)^8287 ≤ (22706280902879/50000000000000 : ℝ)^6239 := by
    have hnat : (689937107 : ℕ)^8287*50000000000000^6239 ≤ 22706280902879^6239*1250000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689937107 1250000000 22706280902879 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132472287/500000000 : ℝ)^8287 ≤ (1070733090243/6250000000000 : ℝ)^6239 := by
    have hnat : (132472287 : ℕ)^8287*6250000000000^6239 ≤ 1070733090243^6239*500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132472287 500000000 1070733090243 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2387185947/5000000000 : ℝ)^8287 ≤ (37455708725281/100000000000000 : ℝ)^6239 := by
    have hnat : (2387185947 : ℕ)^8287*100000000000000^6239 ≤ 37455708725281^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387185947 5000000000 37455708725281 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689937107/1250000000 : ℝ), (-132472287/500000000 : ℝ), (2387185947/5000000000 : ℝ)] ![(22706280902879/50000000000000 : ℝ), (1070733090243/6250000000000 : ℝ), (37455708725281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689937107/1250000000 : ℝ)|^8287 ≤ (22706280902879/50000000000000 : ℝ)^6239
        have hw : |(689937107/1250000000 : ℝ)|=(689937107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132472287/500000000 : ℝ)|^8287 ≤ (1070733090243/6250000000000 : ℝ)^6239
        have hw : |(-132472287/500000000 : ℝ)|=(132472287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2387185947/5000000000 : ℝ)|^8287 ≤ (37455708725281/100000000000000 : ℝ)^6239
        have hw : |(2387185947/5000000000 : ℝ)|=(2387185947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s0_2 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (172484289/312500000 : ℝ)*x 0 + (954874347/2000000000 : ℝ)*x 1 + (-529889087/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172484289/312500000 : ℝ)^8287 ≤ (22706283044857/50000000000000 : ℝ)^6239 := by
    have hnat : (172484289 : ℕ)^8287*50000000000000^6239 ≤ 22706283044857^6239*312500000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172484289 312500000 22706283044857 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (954874347/2000000000 : ℝ)^8287 ≤ (18727853534219/50000000000000 : ℝ)^6239 := by
    have hnat : (954874347 : ℕ)^8287*50000000000000^6239 ≤ 18727853534219^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954874347 2000000000 18727853534219 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529889087/2000000000 : ℝ)^8287 ≤ (2141465853041/12500000000000 : ℝ)^6239 := by
    have hnat : (529889087 : ℕ)^8287*12500000000000^6239 ≤ 2141465853041^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529889087 2000000000 2141465853041 12500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172484289/312500000 : ℝ), (954874347/2000000000 : ℝ), (-529889087/2000000000 : ℝ)] ![(22706283044857/50000000000000 : ℝ), (18727853534219/50000000000000 : ℝ), (2141465853041/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172484289/312500000 : ℝ)|^8287 ≤ (22706283044857/50000000000000 : ℝ)^6239
        have hw : |(172484289/312500000 : ℝ)|=(172484289/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(954874347/2000000000 : ℝ)|^8287 ≤ (18727853534219/50000000000000 : ℝ)^6239
        have hw : |(954874347/2000000000 : ℝ)|=(954874347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529889087/2000000000 : ℝ)|^8287 ≤ (2141465853041/12500000000000 : ℝ)^6239
        have hw : |(-529889087/2000000000 : ℝ)|=(529889087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s0_3 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4204901523/10000000000 : ℝ)*x 0 + (1561703947/5000000000 : ℝ)*x 1 + (113357901/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204901523/10000000000 : ℝ)^8287 ≤ (31641041510541/100000000000000 : ℝ)^6239 := by
    have hnat : (4204901523 : ℕ)^8287*100000000000000^6239 ≤ 31641041510541^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204901523 10000000000 31641041510541 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1561703947/5000000000 : ℝ)^8287 ≤ (2131751941507/10000000000000 : ℝ)^6239 := by
    have hnat : (1561703947 : ℕ)^8287*10000000000000^6239 ≤ 2131751941507^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561703947 5000000000 2131751941507 10000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113357901/200000000 : ℝ)^8287 ≤ (23520719529987/50000000000000 : ℝ)^6239 := by
    have hnat : (113357901 : ℕ)^8287*50000000000000^6239 ≤ 23520719529987^6239*200000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113357901 200000000 23520719529987 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204901523/10000000000 : ℝ), (1561703947/5000000000 : ℝ), (113357901/200000000 : ℝ)] ![(31641041510541/100000000000000 : ℝ), (2131751941507/10000000000000 : ℝ), (23520719529987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204901523/10000000000 : ℝ)|^8287 ≤ (31641041510541/100000000000000 : ℝ)^6239
        have hw : |(4204901523/10000000000 : ℝ)|=(4204901523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1561703947/5000000000 : ℝ)|^8287 ≤ (2131751941507/10000000000000 : ℝ)^6239
        have hw : |(1561703947/5000000000 : ℝ)|=(1561703947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113357901/200000000 : ℝ)|^8287 ≤ (23520719529987/50000000000000 : ℝ)^6239
        have hw : |(113357901/200000000 : ℝ)|=(113357901/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s0_4 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-382477041/2000000000 : ℝ)*x 0 + (2403849959/5000000000 : ℝ)*x 1 + (1206198843/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382477041/2000000000 : ℝ)^8287 ≤ (2222168216887/20000000000000 : ℝ)^6239 := by
    have hnat : (382477041 : ℕ)^8287*20000000000000^6239 ≤ 2222168216887^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382477041 2000000000 2222168216887 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2403849959/5000000000 : ℝ)^8287 ≤ (37803397134519/100000000000000 : ℝ)^6239 := by
    have hnat : (2403849959 : ℕ)^8287*100000000000000^6239 ≤ 37803397134519^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403849959 5000000000 37803397134519 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206198843/2000000000 : ℝ)^8287 ≤ (10217152355061/20000000000000 : ℝ)^6239 := by
    have hnat : (1206198843 : ℕ)^8287*20000000000000^6239 ≤ 10217152355061^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206198843 2000000000 10217152355061 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-382477041/2000000000 : ℝ), (2403849959/5000000000 : ℝ), (1206198843/2000000000 : ℝ)] ![(2222168216887/20000000000000 : ℝ), (37803397134519/100000000000000 : ℝ), (10217152355061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-382477041/2000000000 : ℝ)|^8287 ≤ (2222168216887/20000000000000 : ℝ)^6239
        have hw : |(-382477041/2000000000 : ℝ)|=(382477041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2403849959/5000000000 : ℝ)|^8287 ≤ (37803397134519/100000000000000 : ℝ)^6239
        have hw : |(2403849959/5000000000 : ℝ)|=(2403849959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206198843/2000000000 : ℝ)|^8287 ≤ (10217152355061/20000000000000 : ℝ)^6239
        have hw : |(1206198843/2000000000 : ℝ)|=(1206198843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s0_5 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2584458049/5000000000 : ℝ)*x 0 + (-1392825239/10000000000 : ℝ)*x 1 + (6030994051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584458049/5000000000 : ℝ)^8287 ≤ (41621779727463/100000000000000 : ℝ)^6239 := by
    have hnat : (2584458049 : ℕ)^8287*100000000000000^6239 ≤ 41621779727463^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584458049 5000000000 41621779727463 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1392825239/10000000000 : ℝ)^8287 ≤ (7292460329239/100000000000000 : ℝ)^6239 := by
    have hnat : (1392825239 : ℕ)^8287*100000000000000^6239 ≤ 7292460329239^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392825239 10000000000 7292460329239 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6030994051/10000000000 : ℝ)^8287 ≤ (51085759930131/100000000000000 : ℝ)^6239 := by
    have hnat : (6030994051 : ℕ)^8287*100000000000000^6239 ≤ 51085759930131^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6030994051 10000000000 51085759930131 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584458049/5000000000 : ℝ), (-1392825239/10000000000 : ℝ), (6030994051/10000000000 : ℝ)] ![(41621779727463/100000000000000 : ℝ), (7292460329239/100000000000000 : ℝ), (51085759930131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584458049/5000000000 : ℝ)|^8287 ≤ (41621779727463/100000000000000 : ℝ)^6239
        have hw : |(2584458049/5000000000 : ℝ)|=(2584458049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1392825239/10000000000 : ℝ)|^8287 ≤ (7292460329239/100000000000000 : ℝ)^6239
        have hw : |(-1392825239/10000000000 : ℝ)|=(1392825239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6030994051/10000000000 : ℝ)|^8287 ≤ (51085759930131/100000000000000 : ℝ)^6239
        have hw : |(6030994051/10000000000 : ℝ)|=(6030994051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s0_6 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5168916909/10000000000 : ℝ)*x 0 + (241239779/400000000 : ℝ)*x 1 + (-278564661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168916909/10000000000 : ℝ)^8287 ≤ (20810894200781/50000000000000 : ℝ)^6239 := by
    have hnat : (5168916909 : ℕ)^8287*50000000000000^6239 ≤ 20810894200781^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168916909 10000000000 20810894200781 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241239779/400000000 : ℝ)^8287 ≤ (51085764700579/100000000000000 : ℝ)^6239 := by
    have hnat : (241239779 : ℕ)^8287*100000000000000^6239 ≤ 51085764700579^6239*400000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241239779 400000000 51085764700579 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278564661/2000000000 : ℝ)^8287 ≤ (7292446879429/100000000000000 : ℝ)^6239 := by
    have hnat : (278564661 : ℕ)^8287*100000000000000^6239 ≤ 7292446879429^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278564661 2000000000 7292446879429 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168916909/10000000000 : ℝ), (241239779/400000000 : ℝ), (-278564661/2000000000 : ℝ)] ![(20810894200781/50000000000000 : ℝ), (51085764700579/100000000000000 : ℝ), (7292446879429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168916909/10000000000 : ℝ)|^8287 ≤ (20810894200781/50000000000000 : ℝ)^6239
        have hw : |(5168916909/10000000000 : ℝ)|=(5168916909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241239779/400000000 : ℝ)|^8287 ≤ (51085764700579/100000000000000 : ℝ)^6239
        have hw : |(241239779/400000000 : ℝ)|=(241239779/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278564661/2000000000 : ℝ)|^8287 ≤ (7292446879429/100000000000000 : ℝ)^6239
        have hw : |(-278564661/2000000000 : ℝ)|=(278564661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s0_7 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (168612893/400000000 : ℝ)*x 0 + (560221301/1000000000 : ℝ)*x 1 + (319139259/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168612893/400000000 : ℝ)^8287 ≤ (31745238448187/100000000000000 : ℝ)^6239 := by
    have hnat : (168612893 : ℕ)^8287*100000000000000^6239 ≤ 31745238448187^6239*400000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168612893 400000000 31745238448187 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560221301/1000000000 : ℝ)^8287 ≤ (46318737796751/100000000000000 : ℝ)^6239 := by
    have hnat : (560221301 : ℕ)^8287*100000000000000^6239 ≤ 46318737796751^6239*1000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560221301 1000000000 46318737796751 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319139259/1000000000 : ℝ)^8287 ≤ (21936023745681/100000000000000 : ℝ)^6239 := by
    have hnat : (319139259 : ℕ)^8287*100000000000000^6239 ≤ 21936023745681^6239*1000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319139259 1000000000 21936023745681 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168612893/400000000 : ℝ), (560221301/1000000000 : ℝ), (319139259/1000000000 : ℝ)] ![(31745238448187/100000000000000 : ℝ), (46318737796751/100000000000000 : ℝ), (21936023745681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168612893/400000000 : ℝ)|^8287 ≤ (31745238448187/100000000000000 : ℝ)^6239
        have hw : |(168612893/400000000 : ℝ)|=(168612893/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560221301/1000000000 : ℝ)|^8287 ≤ (46318737796751/100000000000000 : ℝ)^6239
        have hw : |(560221301/1000000000 : ℝ)|=(560221301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319139259/1000000000 : ℝ)|^8287 ≤ (21936023745681/100000000000000 : ℝ)^6239
        have hw : |(319139259/1000000000 : ℝ)|=(319139259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1094_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (107/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7/25 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4143/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4143 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4143*1^1024 ≤ 0^1024*1^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4143/1024 : ℝ) ≤ (2454568410535751157/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4143 ≤ (2454568410535751157/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4143*100000000000000000000^1024 ≤ 2454568410535751157^1024*5^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2454568410535751157 100000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2454568410535751157/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4143 := by
      have hnat : (1 : ℕ)^1024*1^4143 ≤ 1^4143*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102454568410535751157/100000000000000000000 : ℝ) ≤ (5030057717313181/5000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (102454568410535751157/100000000000000000000 : ℝ)^1024 ≤ (5030057717313181/5000000000000000 : ℝ)^4143 := by
      have hnat : (102454568410535751157 : ℕ)^1024*5000000000000000^4143 ≤ 5030057717313181^4143*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102454568410535751157 100000000000000000000 5030057717313181 5000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030057717313181/5000000000000000 : ℝ)) (X := (102454568410535751157/100000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52454568410535751157/50000000000000000000 : ℝ) ≤ (2530057717313181/2500000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (52454568410535751157/50000000000000000000 : ℝ)^1024 ≤ (2530057717313181/2500000000000000 : ℝ)^4143 := by
      have hnat : (52454568410535751157 : ℕ)^1024*2500000000000000^4143 ≤ 2530057717313181^4143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52454568410535751157 50000000000000000000 2530057717313181 2500000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530057717313181/2500000000000000 : ℝ)) (X := (52454568410535751157/50000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30057717313181/2000000000000000 : ℝ)*(0 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30057717313181/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2454568410535751157/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30057717313181/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4143/1024 : ℝ) := by
    rw [show (1 : ℝ)+(30057717313181/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030057717313181/5000000000000000 : ℝ) by norm_num, show 1+(2454568410535751157/100000000000000000000 : ℝ)+(0 : ℝ)=(102454568410535751157/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2454568410535751157/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30057717313181/2000000000000000 : ℝ)*(2/5 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30057717313181/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530057717313181/2500000000000000 : ℝ) by norm_num, show 1+2*(2454568410535751157/100000000000000000000 : ℝ)=(52454568410535751157/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30057717313181/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30057717313181/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30057717313181/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30057717313181/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30057717313181/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30057717313181/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1907096263/10000000000 : ℝ)*X 0 0+(606549077/1000000000 : ℝ)*X 0 1+(4774371753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((689937107/1250000000 : ℝ)*X 1 0+(-132472287/500000000 : ℝ)*X 1 1+(2387185947/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((172484289/312500000 : ℝ)*X 2 0+(954874347/2000000000 : ℝ)*X 2 1+(-529889087/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4204901523/10000000000 : ℝ)*X 0 0+(1561703947/5000000000 : ℝ)*X 0 1+(113357901/200000000 : ℝ)*X 0 2+(4204901523/10000000000 : ℝ)*X 1 0+(1561703947/5000000000 : ℝ)*X 1 1+(113357901/200000000 : ℝ)*X 1 2+(4204901523/10000000000 : ℝ)*X 2 0+(1561703947/5000000000 : ℝ)*X 2 1+(113357901/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-382477041/2000000000 : ℝ)*X 0 0+(2403849959/5000000000 : ℝ)*X 0 1+(1206198843/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2584458049/5000000000 : ℝ)*X 1 0+(-1392825239/10000000000 : ℝ)*X 1 1+(6030994051/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168916909/10000000000 : ℝ)*X 2 0+(241239779/400000000 : ℝ)*X 2 1+(-278564661/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((168612893/400000000 : ℝ)*X 0 0+(560221301/1000000000 : ℝ)*X 0 1+(319139259/1000000000 : ℝ)*X 0 2+(168612893/400000000 : ℝ)*X 1 0+(560221301/1000000000 : ℝ)*X 1 1+(319139259/1000000000 : ℝ)*X 1 2+(168612893/400000000 : ℝ)*X 2 0+(560221301/1000000000 : ℝ)*X 2 1+(319139259/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14587711866668136262113/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19947887/50000000000000 : ℝ)*(base1) + (1537402237/100000000000000 : ℝ)*(base19) + (1456002659/100000000000000 : ℝ)*(base23) + (17050921/12500000000000 : ℝ)*(base24) + (363645957/100000000000000 : ℝ)*(upper3) + (29188541878491/5000000000000 : ℝ)*(major0) + (29188541878491/5000000000000 : ℝ)*(major1) + (29188541878491/5000000000000 : ℝ)*(major2) + (387263538531307/50000000000000 : ℝ)*(sp0) + (387264467249467/50000000000000 : ℝ)*(sp1) + (96816109936393/12500000000000 : ℝ)*(sp2) + (393008140208689/100000000000000 : ℝ)*(sp3) + (3434734331/100000000000000 : ℝ)*(sp4) + (1414315589/50000000000000 : ℝ)*(sp7) + (393011008735641/100000000000000 : ℝ)*(f.failure) + (774530471901171/100000000000000 : ℝ)*(f.sum) + (1610894610129/5000000000000000000000000000 : ℝ)*base66 + (14171350849871/10000000000000000000000000000 : ℝ)*base67 + (17191885080129/10000000000000000000000000000 : ℝ)*base70 + (11168242320129/10000000000000000000000000000 : ℝ)*base72 + (6637216759871/5000000000000000000000000000 : ℝ)*base73 + (3649119970129/10000000000000000000000000000 : ℝ)*base76 + (20831555599871/10000000000000000000000000000 : ℝ)*base77 + (22497221170129/10000000000000000000000000000 : ℝ)*base80 + (17743569460129/5000000000000000000000000000 : ℝ)*base82 + (33923283/10000000000000000000000 : ℝ)*base90 + (33923283/10000000000000000000000 : ℝ)*base92 + (33923283/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47162927750244432964971/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85161873/25000000000000 : ℝ)*(base19) + (116131901/12500000000000 : ℝ)*(base23) + (111083817/25000000000000 : ℝ)*(base39) + (50449329/50000000000000 : ℝ)*(base45) + (10449077/50000000000000 : ℝ)*(upper3) + (141166471/50000000000000 : ℝ)*(upper5) + (154032288359211/25000000000000 : ℝ)*(major0) + (154032288359211/25000000000000 : ℝ)*(major1) + (77016088637697/12500000000000 : ℝ)*(major2) + (423627491/100000000000000 : ℝ)*(sp2) + (102182774532597/12500000000000 : ℝ)*(sp4) + (163492371122657/20000000000000 : ℝ)*(sp5) + (163492257582669/20000000000000 : ℝ)*(sp6) + (51849442563729/12500000000000 : ℝ)*(sp7) + (51849442563729/12500000000000 : ℝ)*(f.failure) + (204365660149011/25000000000000 : ℝ)*(f.sum) + (307936045701/10000000000000000000000000000 : ℝ)*base65 + (201014875615843/25000000000000000000000000000 : ℝ)*base68 + (76964127060191/50000000000000000000000000000 : ℝ)*base69 + (142655641665843/25000000000000000000000000000 : ℝ)*base72 + (32934402804299/10000000000000000000000000000 : ℝ)*base74 + (328243707689809/50000000000000000000000000000 : ℝ)*base76 + (143342825589809/50000000000000000000000000000 : ℝ)*base78 + (157140590939809/50000000000000000000000000000 : ℝ)*base80 + (75682261310191/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3059973/1250000000000000000000 : ℝ)*base89 + (3059973/1250000000000000000000 : ℝ)*base91 + (3059973/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1094_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (107/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7/25 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1094_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1094_s1_0 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528805797/2500000000 : ℝ)*x 0 + (1428633249/2500000000 : ℝ)*x 1 + (4992062639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528805797/2500000000 : ℝ)^8287 ≤ (12702791026317/100000000000000 : ℝ)^6239 := by
    have hnat : (528805797 : ℕ)^8287*100000000000000^6239 ≤ 12702791026317^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528805797 2500000000 12702791026317 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1428633249/2500000000 : ℝ)^8287 ≤ (47556271164879/100000000000000 : ℝ)^6239 := by
    have hnat : (1428633249 : ℕ)^8287*100000000000000^6239 ≤ 47556271164879^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428633249 2500000000 47556271164879 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4992062639/10000000000 : ℝ)^8287 ≤ (39740937799763/100000000000000 : ℝ)^6239 := by
    have hnat : (4992062639 : ℕ)^8287*100000000000000^6239 ≤ 39740937799763^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992062639 10000000000 39740937799763 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528805797/2500000000 : ℝ), (1428633249/2500000000 : ℝ), (4992062639/10000000000 : ℝ)] ![(12702791026317/100000000000000 : ℝ), (47556271164879/100000000000000 : ℝ), (39740937799763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528805797/2500000000 : ℝ)|^8287 ≤ (12702791026317/100000000000000 : ℝ)^6239
        have hw : |(-528805797/2500000000 : ℝ)|=(528805797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1428633249/2500000000 : ℝ)|^8287 ≤ (47556271164879/100000000000000 : ℝ)^6239
        have hw : |(1428633249/2500000000 : ℝ)|=(1428633249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4992062639/10000000000 : ℝ)|^8287 ≤ (39740937799763/100000000000000 : ℝ)^6239
        have hw : |(4992062639/10000000000 : ℝ)|=(4992062639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s1_1 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1355441119/2500000000 : ℝ)*x 0 + (-25060769/100000000 : ℝ)*x 1 + (4992062821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355441119/2500000000 : ℝ)^8287 ≤ (1385862938973/3125000000000 : ℝ)^6239 := by
    have hnat : (1355441119 : ℕ)^8287*3125000000000^6239 ≤ 1385862938973^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355441119 2500000000 1385862938973 3125000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25060769/100000000 : ℝ)^8287 ≤ (3977861553153/25000000000000 : ℝ)^6239 := by
    have hnat : (25060769 : ℕ)^8287*25000000000000^6239 ≤ 3977861553153^6239*100000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25060769 100000000 3977861553153 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4992062821/10000000000 : ℝ)^8287 ≤ (9935234931059/25000000000000 : ℝ)^6239 := by
    have hnat : (4992062821 : ℕ)^8287*25000000000000^6239 ≤ 9935234931059^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992062821 10000000000 9935234931059 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355441119/2500000000 : ℝ), (-25060769/100000000 : ℝ), (4992062821/10000000000 : ℝ)] ![(1385862938973/3125000000000 : ℝ), (3977861553153/25000000000000 : ℝ), (9935234931059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355441119/2500000000 : ℝ)|^8287 ≤ (1385862938973/3125000000000 : ℝ)^6239
        have hw : |(1355441119/2500000000 : ℝ)|=(1355441119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25060769/100000000 : ℝ)|^8287 ≤ (3977861553153/25000000000000 : ℝ)^6239
        have hw : |(-25060769/100000000 : ℝ)|=(25060769/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4992062821/10000000000 : ℝ)|^8287 ≤ (9935234931059/25000000000000 : ℝ)^6239
        have hw : |(4992062821/10000000000 : ℝ)|=(4992062821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s1_2 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5421765443/10000000000 : ℝ)*x 0 + (4992061847/10000000000 : ℝ)*x 1 + (-626519219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421765443/10000000000 : ℝ)^8287 ≤ (44347624553161/100000000000000 : ℝ)^6239 := by
    have hnat : (5421765443 : ℕ)^8287*100000000000000^6239 ≤ 44347624553161^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421765443 10000000000 44347624553161 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4992061847/10000000000 : ℝ)^8287 ≤ (39740929425133/100000000000000 : ℝ)^6239 := by
    have hnat : (4992061847 : ℕ)^8287*100000000000000^6239 ≤ 39740929425133^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992061847 10000000000 39740929425133 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626519219/2500000000 : ℝ)^8287 ≤ (15911446010213/100000000000000 : ℝ)^6239 := by
    have hnat : (626519219 : ℕ)^8287*100000000000000^6239 ≤ 15911446010213^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626519219 2500000000 15911446010213 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421765443/10000000000 : ℝ), (4992061847/10000000000 : ℝ), (-626519219/2500000000 : ℝ)] ![(44347624553161/100000000000000 : ℝ), (39740929425133/100000000000000 : ℝ), (15911446010213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421765443/10000000000 : ℝ)|^8287 ≤ (44347624553161/100000000000000 : ℝ)^6239
        have hw : |(5421765443/10000000000 : ℝ)|=(5421765443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4992061847/10000000000 : ℝ)|^8287 ≤ (39740929425133/100000000000000 : ℝ)^6239
        have hw : |(4992061847/10000000000 : ℝ)|=(4992061847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-626519219/2500000000 : ℝ)|^8287 ≤ (15911446010213/100000000000000 : ℝ)^6239
        have hw : |(-626519219/2500000000 : ℝ)|=(626519219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s1_3 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2160737773/5000000000 : ℝ)*x 0 + (1833968961/5000000000 : ℝ)*x 1 + (15911727/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160737773/5000000000 : ℝ)^8287 ≤ (32811453206197/100000000000000 : ℝ)^6239 := by
    have hnat : (2160737773 : ℕ)^8287*100000000000000^6239 ≤ 32811453206197^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160737773 5000000000 32811453206197 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1833968961/5000000000 : ℝ)^8287 ≤ (824688889879/3125000000000 : ℝ)^6239 := by
    have hnat : (1833968961 : ℕ)^8287*3125000000000^6239 ≤ 824688889879^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833968961 5000000000 824688889879 3125000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15911727/31250000 : ℝ)^8287 ≤ (5099812787689/12500000000000 : ℝ)^6239 := by
    have hnat : (15911727 : ℕ)^8287*12500000000000^6239 ≤ 5099812787689^6239*31250000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15911727 31250000 5099812787689 12500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160737773/5000000000 : ℝ), (1833968961/5000000000 : ℝ), (15911727/31250000 : ℝ)] ![(32811453206197/100000000000000 : ℝ), (824688889879/3125000000000 : ℝ), (5099812787689/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160737773/5000000000 : ℝ)|^8287 ≤ (32811453206197/100000000000000 : ℝ)^6239
        have hw : |(2160737773/5000000000 : ℝ)|=(2160737773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1833968961/5000000000 : ℝ)|^8287 ≤ (824688889879/3125000000000 : ℝ)^6239
        have hw : |(1833968961/5000000000 : ℝ)|=(1833968961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15911727/31250000 : ℝ)|^8287 ≤ (5099812787689/12500000000000 : ℝ)^6239
        have hw : |(15911727/31250000 : ℝ)|=(15911727/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s1_4 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116098781/10000000000 : ℝ)*x 0 + (2501054789/5000000000 : ℝ)*x 1 + (5704283989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116098781/10000000000 : ℝ)^8287 ≤ (12709775876437/100000000000000 : ℝ)^6239 := by
    have hnat : (2116098781 : ℕ)^8287*100000000000000^6239 ≤ 12709775876437^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116098781 10000000000 12709775876437 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2501054789/5000000000 : ℝ)^8287 ≤ (9961802371581/25000000000000 : ℝ)^6239 := by
    have hnat : (2501054789 : ℕ)^8287*25000000000000^6239 ≤ 9961802371581^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501054789 5000000000 9961802371581 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5704283989/10000000000 : ℝ)^8287 ≤ (47443014626969/100000000000000 : ℝ)^6239 := by
    have hnat : (5704283989 : ℕ)^8287*100000000000000^6239 ≤ 47443014626969^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704283989 10000000000 47443014626969 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116098781/10000000000 : ℝ), (2501054789/5000000000 : ℝ), (5704283989/10000000000 : ℝ)] ![(12709775876437/100000000000000 : ℝ), (9961802371581/25000000000000 : ℝ), (47443014626969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116098781/10000000000 : ℝ)|^8287 ≤ (12709775876437/100000000000000 : ℝ)^6239
        have hw : |(-2116098781/10000000000 : ℝ)|=(2116098781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2501054789/5000000000 : ℝ)|^8287 ≤ (9961802371581/25000000000000 : ℝ)^6239
        have hw : |(2501054789/5000000000 : ℝ)|=(2501054789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5704283989/10000000000 : ℝ)|^8287 ≤ (47443014626969/100000000000000 : ℝ)^6239
        have hw : |(5704283989/10000000000 : ℝ)|=(5704283989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s1_5 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (523698781/1000000000 : ℝ)*x 0 + (-1793855461/10000000000 : ℝ)*x 1 + (2852141913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523698781/1000000000 : ℝ)^8287 ≤ (21175706937309/50000000000000 : ℝ)^6239 := by
    have hnat : (523698781 : ℕ)^8287*50000000000000^6239 ≤ 21175706937309^6239*1000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523698781 1000000000 21175706937309 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793855461/10000000000 : ℝ)^8287 ≤ (2551393321043/25000000000000 : ℝ)^6239 := by
    have hnat : (1793855461 : ℕ)^8287*25000000000000^6239 ≤ 2551393321043^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793855461 10000000000 2551393321043 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2852141913/5000000000 : ℝ)^8287 ≤ (4744301282627/10000000000000 : ℝ)^6239 := by
    have hnat : (2852141913 : ℕ)^8287*10000000000000^6239 ≤ 4744301282627^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852141913 5000000000 4744301282627 10000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523698781/1000000000 : ℝ), (-1793855461/10000000000 : ℝ), (2852141913/5000000000 : ℝ)] ![(21175706937309/50000000000000 : ℝ), (2551393321043/25000000000000 : ℝ), (4744301282627/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523698781/1000000000 : ℝ)|^8287 ≤ (21175706937309/50000000000000 : ℝ)^6239
        have hw : |(523698781/1000000000 : ℝ)|=(523698781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793855461/10000000000 : ℝ)|^8287 ≤ (2551393321043/25000000000000 : ℝ)^6239
        have hw : |(-1793855461/10000000000 : ℝ)|=(1793855461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2852141913/5000000000 : ℝ)|^8287 ≤ (4744301282627/10000000000000 : ℝ)^6239
        have hw : |(2852141913/5000000000 : ℝ)|=(2852141913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s1_6 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (523698783/1000000000 : ℝ)*x 0 + (114085679/200000000 : ℝ)*x 1 + (-1793855251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523698783/1000000000 : ℝ)^8287 ≤ (847028281789/2000000000000 : ℝ)^6239 := by
    have hnat : (523698783 : ℕ)^8287*2000000000000^6239 ≤ 847028281789^6239*1000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523698783 1000000000 847028281789 2000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114085679/200000000 : ℝ)^8287 ≤ (47443014196127/100000000000000 : ℝ)^6239 := by
    have hnat : (114085679 : ℕ)^8287*100000000000000^6239 ≤ 47443014196127^6239*200000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114085679 200000000 47443014196127 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1793855251/10000000000 : ℝ)^8287 ≤ (637848231079/6250000000000 : ℝ)^6239 := by
    have hnat : (1793855251 : ℕ)^8287*6250000000000^6239 ≤ 637848231079^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793855251 10000000000 637848231079 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523698783/1000000000 : ℝ), (114085679/200000000 : ℝ), (-1793855251/10000000000 : ℝ)] ![(847028281789/2000000000000 : ℝ), (47443014196127/100000000000000 : ℝ), (637848231079/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523698783/1000000000 : ℝ)|^8287 ≤ (847028281789/2000000000000 : ℝ)^6239
        have hw : |(523698783/1000000000 : ℝ)|=(523698783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(114085679/200000000 : ℝ)|^8287 ≤ (47443014196127/100000000000000 : ℝ)^6239
        have hw : |(114085679/200000000 : ℝ)|=(114085679/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1793855251/10000000000 : ℝ)|^8287 ≤ (637848231079/6250000000000 : ℝ)^6239
        have hw : |(-1793855251/10000000000 : ℝ)|=(1793855251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s1_7 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4323200199/10000000000 : ℝ)*x 0 + (5071953289/10000000000 : ℝ)*x 1 + (3688135521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323200199/10000000000 : ℝ)^8287 ≤ (16414423732567/50000000000000 : ℝ)^6239 := by
    have hnat : (4323200199 : ℕ)^8287*50000000000000^6239 ≤ 16414423732567^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323200199 10000000000 16414423732567 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5071953289/10000000000 : ℝ)^8287 ≤ (10146978683667/25000000000000 : ℝ)^6239 := by
    have hnat : (5071953289 : ℕ)^8287*25000000000000^6239 ≤ 10146978683667^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071953289 10000000000 10146978683667 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3688135521/10000000000 : ℝ)^8287 ≤ (26583237789553/100000000000000 : ℝ)^6239 := by
    have hnat : (3688135521 : ℕ)^8287*100000000000000^6239 ≤ 26583237789553^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688135521 10000000000 26583237789553 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323200199/10000000000 : ℝ), (5071953289/10000000000 : ℝ), (3688135521/10000000000 : ℝ)] ![(16414423732567/50000000000000 : ℝ), (10146978683667/25000000000000 : ℝ), (26583237789553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323200199/10000000000 : ℝ)|^8287 ≤ (16414423732567/50000000000000 : ℝ)^6239
        have hw : |(4323200199/10000000000 : ℝ)|=(4323200199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5071953289/10000000000 : ℝ)|^8287 ≤ (10146978683667/25000000000000 : ℝ)^6239
        have hw : |(5071953289/10000000000 : ℝ)|=(5071953289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3688135521/10000000000 : ℝ)|^8287 ≤ (26583237789553/100000000000000 : ℝ)^6239
        have hw : |(3688135521/10000000000 : ℝ)|=(3688135521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1094_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/25 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (107/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5377/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10329/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7/25 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (107/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7/25 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (107/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7/25 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (107/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7/25 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (107/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7/25 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (107/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7/25 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (107/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (107/50000 : ℝ) ^ (4143/1024 : ℝ) ≤ (9885651/625000000000000000 : ℝ) := by
    have hpowers : (107/50000 : ℝ)^4143 ≤ (9885651/625000000000000000 : ℝ)^1024 := by
      have hnat : (107 : ℕ)^4143*625000000000000000^1024 ≤ 9885651^1024*50000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107 50000 9885651 625000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (107/50000 : ℝ)) (X := (9885651/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7/25 : ℝ) ^ (4143/1024 : ℝ) ≤ (289886203906162899/50000000000000000000 : ℝ) := by
    have hpowers : (7/25 : ℝ)^4143 ≤ (289886203906162899/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7 : ℕ)^4143*50000000000000000000^1024 ≤ 289886203906162899^1024*25^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7 25 289886203906162899 50000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7/25 : ℝ)) (X := (289886203906162899/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (312500000009885651/312500000000000000 : ℝ) ≤ (10000000000078189/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (312500000009885651/312500000000000000 : ℝ)^1024 ≤ (10000000000078189/10000000000000000 : ℝ)^4143 := by
      have hnat : (312500000009885651 : ℕ)^1024*10000000000000000^4143 ≤ 10000000000078189^4143*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312500000009885651 312500000000000000 10000000000078189 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000078189/10000000000000000 : ℝ)) (X := (312500000009885651/312500000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50289886204697014979/50000000000000000000 : ℝ) ≤ (10014298712897609/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (50289886204697014979/50000000000000000000 : ℝ)^1024 ≤ (10014298712897609/10000000000000000 : ℝ)^4143 := by
      have hnat : (50289886204697014979 : ℕ)^1024*10000000000000000^4143 ≤ 10014298712897609^4143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50289886204697014979 50000000000000000000 10014298712897609 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014298712897609/10000000000000000 : ℝ)) (X := (50289886204697014979/50000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25289886203906162899/25000000000000000000 : ℝ) ≤ (10028597425717029/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (25289886203906162899/25000000000000000000 : ℝ)^1024 ≤ (10028597425717029/10000000000000000 : ℝ)^4143 := by
      have hnat : (25289886203906162899 : ℕ)^1024*10000000000000000^4143 ≤ 10028597425717029^4143*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25289886203906162899 25000000000000000000 10028597425717029 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028597425717029/10000000000000000 : ℝ)) (X := (25289886203906162899/25000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9885651/625000000000000000 : ℝ) ≤ ((138926940076542923897/138930000000000000000 : ℝ)+2*(714935640971/138930000000000 : ℝ)*(107/50000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (138926940076542923897/138930000000000000000 : ℝ)+2*(714935640971/138930000000000 : ℝ)*(107/50000 : ℝ)=(10000000000078189/10000000000000000 : ℝ) by norm_num, show 1+2*(9885651/625000000000000000 : ℝ)=(312500000009885651/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(289886203906162899/50000000000000000000 : ℝ)+(9885651/625000000000000000 : ℝ) ≤ ((138926940076542923897/138930000000000000000 : ℝ)+(714935640971/138930000000000 : ℝ)*((7/25 : ℝ)+(107/50000 : ℝ)))^(4143/1024 : ℝ) := by
    rw [show (138926940076542923897/138930000000000000000 : ℝ)+(714935640971/138930000000000 : ℝ)*((7/25 : ℝ)+(107/50000 : ℝ))=(10014298712897609/10000000000000000 : ℝ) by norm_num, show 1+(289886203906162899/50000000000000000000 : ℝ)+(9885651/625000000000000000 : ℝ)=(50289886204697014979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(289886203906162899/50000000000000000000 : ℝ) ≤ ((138926940076542923897/138930000000000000000 : ℝ)+2*(714935640971/138930000000000 : ℝ)*(7/25 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (138926940076542923897/138930000000000000000 : ℝ)+2*(714935640971/138930000000000 : ℝ)*(7/25 : ℝ)=(10028597425717029/10000000000000000 : ℝ) by norm_num, show 1+2*(289886203906162899/50000000000000000000 : ℝ)=(25289886203906162899/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (138926940076542923897/138930000000000000000 : ℝ)*(X 1 0+X 2 0)+(714935640971/138930000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (107/50000 : ℝ)) (hi := (7/25 : ℝ)) (c := (138926940076542923897/138930000000000000000 : ℝ)) (alpha := (714935640971/138930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (138926940076542923897/138930000000000000000 : ℝ)*(X 0 1+X 2 1)+(714935640971/138930000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (107/50000 : ℝ)) (hi := (7/25 : ℝ)) (c := (138926940076542923897/138930000000000000000 : ℝ)) (alpha := (714935640971/138930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (138926940076542923897/138930000000000000000 : ℝ)*(X 0 2+X 1 2)+(714935640971/138930000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (107/50000 : ℝ)) (hi := (7/25 : ℝ)) (c := (138926940076542923897/138930000000000000000 : ℝ)) (alpha := (714935640971/138930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-528805797/2500000000 : ℝ)*X 0 0+(1428633249/2500000000 : ℝ)*X 0 1+(4992062639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1355441119/2500000000 : ℝ)*X 1 0+(-25060769/100000000 : ℝ)*X 1 1+(4992062821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5421765443/10000000000 : ℝ)*X 2 0+(4992061847/10000000000 : ℝ)*X 2 1+(-626519219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2160737773/5000000000 : ℝ)*X 0 0+(1833968961/5000000000 : ℝ)*X 0 1+(15911727/31250000 : ℝ)*X 0 2+(2160737773/5000000000 : ℝ)*X 1 0+(1833968961/5000000000 : ℝ)*X 1 1+(15911727/31250000 : ℝ)*X 1 2+(2160737773/5000000000 : ℝ)*X 2 0+(1833968961/5000000000 : ℝ)*X 2 1+(15911727/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2116098781/10000000000 : ℝ)*X 0 0+(2501054789/5000000000 : ℝ)*X 0 1+(5704283989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((523698781/1000000000 : ℝ)*X 1 0+(-1793855461/10000000000 : ℝ)*X 1 1+(2852141913/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((523698783/1000000000 : ℝ)*X 2 0+(114085679/200000000 : ℝ)*X 2 1+(-1793855251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4323200199/10000000000 : ℝ)*X 0 0+(5071953289/10000000000 : ℝ)*X 0 1+(3688135521/10000000000 : ℝ)*X 0 2+(4323200199/10000000000 : ℝ)*X 1 0+(5071953289/10000000000 : ℝ)*X 1 1+(3688135521/10000000000 : ℝ)*X 1 2+(4323200199/10000000000 : ℝ)*X 2 0+(5071953289/10000000000 : ℝ)*X 2 1+(3688135521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8196563682040807307111/4631000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126700357/100000000000000 : ℝ)*(base1) + (6236399/2500000000000 : ℝ)*(base19) + (99267443/20000000000000 : ℝ)*(base23) + (3630931/100000000000000 : ℝ)*(base24) + (47571853/100000000000000 : ℝ)*(upper5) + (1043240044485007/100000000000000 : ℝ)*(major0) + (1043240044485007/100000000000000 : ℝ)*(major1) + (1043240044485007/100000000000000 : ℝ)*(major2) + (692070089816539/50000000000000 : ℝ)*(sp0) + (1384141023150043/100000000000000 : ℝ)*(sp1) + (27682817590889/2000000000000 : ℝ)*(sp2) + (35116926187963/5000000000000 : ℝ)*(sp3) + (331644969/25000000000000 : ℝ)*(sp4) + (53453297/50000000000000 : ℝ)*(sp5) + (702338650459617/100000000000000 : ℝ)*(f.failure) + (346035344878149/25000000000000 : ℝ)*(f.sum) + (9320618241287/6946500000000000000000000000 : ℝ)*base65 + (4042354314644771611/1263000000000000000000000000000000 : ℝ)*base68 + (1213073749454771611/1263000000000000000000000000000000 : ℝ)*base70 + (1584821149539228389/1263000000000000000000000000000000 : ℝ)*base71 + (154156471039/217078125000000000000000000 : ℝ)*base73 + (2227290208337771611/1263000000000000000000000000000000 : ℝ)*base76 + (3794376825393228389/1263000000000000000000000000000000 : ℝ)*base77 + (428785501113228389/1263000000000000000000000000000000 : ℝ)*base79 + (29645051489503/6946500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (43048171/10000000000000000000000 : ℝ)*base90 + (43048171/10000000000000000000000 : ℝ)*base92 + (43048171/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12568579193750505832581/4631000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35770329/100000000000000 : ℝ)*(base1) + (625475289/100000000000000 : ℝ)*(base19) + (645646727/100000000000000 : ℝ)*(base23) + (29047279/50000000000000 : ℝ)*(upper3) + (11722589/20000000000000 : ℝ)*(upper5) + (1073393134869021/100000000000000 : ℝ)*(major0) + (1073393134869021/100000000000000 : ℝ)*(major1) + (1073393134869021/100000000000000 : ℝ)*(major2) + (2344410733/100000000000000 : ℝ)*(sp1) + (2761952747/100000000000000 : ℝ)*(sp2) + (712073826430073/50000000000000 : ℝ)*(sp4) + (284828929440759/20000000000000 : ℝ)*(sp5) + (1424144209490343/100000000000000 : ℝ)*(sp6) + (7226385264109/1000000000000 : ℝ)*(sp7) + (722638562181229/100000000000000 : ℝ)*(f.failure) + (1424147617089817/100000000000000 : ℝ)*(f.sum) + (44435779999/46310000000000000000000000 : ℝ)*base65 + (877074324456754389/421000000000000000000000000000000 : ℝ)*base67 + (3835621906869245611/421000000000000000000000000000000 : ℝ)*base70 + (532223373413245611/421000000000000000000000000000000 : ℝ)*base72 + (23084645831539/4631000000000000000000000000 : ℝ)*base73 + (196305589081754389/421000000000000000000000000000000 : ℝ)*base75 + (1097958017426245611/421000000000000000000000000000000 : ℝ)*base78 + (1984573692465754389/421000000000000000000000000000000 : ℝ)*base79 + (22065064203891/4631000000000000000000000000 : ℝ)*base82 + (93907473/10000000000000000000000 : ℝ)*base89 + (93907473/10000000000000000000000 : ℝ)*base91 + (93907473/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1094_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/25 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (107/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10329/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1094_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1094_s2_0 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085538039/5000000000 : ℝ)*x 0 + (5520181807/10000000000 : ℝ)*x 1 + (5150948707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085538039/5000000000 : ℝ)^8287 ≤ (13150234420381/100000000000000 : ℝ)^6239 := by
    have hnat : (1085538039 : ℕ)^8287*100000000000000^6239 ≤ 13150234420381^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085538039 5000000000 13150234420381 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5520181807/10000000000 : ℝ)^8287 ≤ (45420047416061/100000000000000 : ℝ)^6239 := by
    have hnat : (5520181807 : ℕ)^8287*100000000000000^6239 ≤ 45420047416061^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520181807 10000000000 45420047416061 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150948707/10000000000 : ℝ)^8287 ≤ (20714859073481/50000000000000 : ℝ)^6239 := by
    have hnat : (5150948707 : ℕ)^8287*50000000000000^6239 ≤ 20714859073481^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150948707 10000000000 20714859073481 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085538039/5000000000 : ℝ), (5520181807/10000000000 : ℝ), (5150948707/10000000000 : ℝ)] ![(13150234420381/100000000000000 : ℝ), (45420047416061/100000000000000 : ℝ), (20714859073481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085538039/5000000000 : ℝ)|^8287 ≤ (13150234420381/100000000000000 : ℝ)^6239
        have hw : |(-1085538039/5000000000 : ℝ)|=(1085538039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5520181807/10000000000 : ℝ)|^8287 ≤ (45420047416061/100000000000000 : ℝ)^6239
        have hw : |(5520181807/10000000000 : ℝ)|=(5520181807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150948707/10000000000 : ℝ)|^8287 ≤ (20714859073481/50000000000000 : ℝ)^6239
        have hw : |(5150948707/10000000000 : ℝ)|=(5150948707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s2_1 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5375953221/10000000000 : ℝ)*x 0 + (-1181705129/5000000000 : ℝ)*x 1 + (2575474877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375953221/10000000000 : ℝ)^8287 ≤ (2740661667113/6250000000000 : ℝ)^6239 := by
    have hnat : (5375953221 : ℕ)^8287*6250000000000^6239 ≤ 2740661667113^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375953221 10000000000 2740661667113 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1181705129/5000000000 : ℝ)^8287 ≤ (3679920996033/25000000000000 : ℝ)^6239 := by
    have hnat : (1181705129 : ℕ)^8287*25000000000000^6239 ≤ 3679920996033^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181705129 5000000000 3679920996033 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575474877/5000000000 : ℝ)^8287 ≤ (41429729332421/100000000000000 : ℝ)^6239 := by
    have hnat : (2575474877 : ℕ)^8287*100000000000000^6239 ≤ 41429729332421^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575474877 5000000000 41429729332421 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375953221/10000000000 : ℝ), (-1181705129/5000000000 : ℝ), (2575474877/5000000000 : ℝ)] ![(2740661667113/6250000000000 : ℝ), (3679920996033/25000000000000 : ℝ), (41429729332421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375953221/10000000000 : ℝ)|^8287 ≤ (2740661667113/6250000000000 : ℝ)^6239
        have hw : |(5375953221/10000000000 : ℝ)|=(5375953221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1181705129/5000000000 : ℝ)|^8287 ≤ (3679920996033/25000000000000 : ℝ)^6239
        have hw : |(-1181705129/5000000000 : ℝ)|=(1181705129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575474877/5000000000 : ℝ)|^8287 ≤ (41429729332421/100000000000000 : ℝ)^6239
        have hw : |(2575474877/5000000000 : ℝ)|=(2575474877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s2_2 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1343988293/2500000000 : ℝ)*x 0 + (5150949801/10000000000 : ℝ)*x 1 + (-2363410261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343988293/2500000000 : ℝ)^8287 ≤ (1754023445717/4000000000000 : ℝ)^6239 := by
    have hnat : (1343988293 : ℕ)^8287*4000000000000^6239 ≤ 1754023445717^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343988293 2500000000 1754023445717 4000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150949801/10000000000 : ℝ)^8287 ≤ (20714864917269/50000000000000 : ℝ)^6239 := by
    have hnat : (5150949801 : ℕ)^8287*50000000000000^6239 ≤ 20714864917269^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150949801 10000000000 20714864917269 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2363410261/10000000000 : ℝ)^8287 ≤ (294393680179/2000000000000 : ℝ)^6239 := by
    have hnat : (2363410261 : ℕ)^8287*2000000000000^6239 ≤ 294393680179^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2363410261 10000000000 294393680179 2000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343988293/2500000000 : ℝ), (5150949801/10000000000 : ℝ), (-2363410261/10000000000 : ℝ)] ![(1754023445717/4000000000000 : ℝ), (20714864917269/50000000000000 : ℝ), (294393680179/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343988293/2500000000 : ℝ)|^8287 ≤ (1754023445717/4000000000000 : ℝ)^6239
        have hw : |(1343988293/2500000000 : ℝ)|=(1343988293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150949801/10000000000 : ℝ)|^8287 ≤ (20714864917269/50000000000000 : ℝ)^6239
        have hw : |(5150949801/10000000000 : ℝ)|=(5150949801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2363410261/10000000000 : ℝ)|^8287 ≤ (294393680179/2000000000000 : ℝ)^6239
        have hw : |(-2363410261/10000000000 : ℝ)|=(2363410261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s2_3 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359665319/10000000000 : ℝ)*x 0 + (2005521781/5000000000 : ℝ)*x 1 + (1184677981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359665319/10000000000 : ℝ)^8287 ≤ (8299288616597/25000000000000 : ℝ)^6239 := by
    have hnat : (4359665319 : ℕ)^8287*25000000000000^6239 ≤ 8299288616597^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359665319 10000000000 8299288616597 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005521781/5000000000 : ℝ)^8287 ≤ (1857391964281/6250000000000 : ℝ)^6239 := by
    have hnat : (2005521781 : ℕ)^8287*6250000000000^6239 ≤ 1857391964281^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005521781 5000000000 1857391964281 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184677981/2500000000 : ℝ)^8287 ≤ (37084574090659/100000000000000 : ℝ)^6239 := by
    have hnat : (1184677981 : ℕ)^8287*100000000000000^6239 ≤ 37084574090659^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184677981 2500000000 37084574090659 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359665319/10000000000 : ℝ), (2005521781/5000000000 : ℝ), (1184677981/2500000000 : ℝ)] ![(8299288616597/25000000000000 : ℝ), (1857391964281/6250000000000 : ℝ), (37084574090659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359665319/10000000000 : ℝ)|^8287 ≤ (8299288616597/25000000000000 : ℝ)^6239
        have hw : |(4359665319/10000000000 : ℝ)|=(4359665319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2005521781/5000000000 : ℝ)|^8287 ≤ (1857391964281/6250000000000 : ℝ)^6239
        have hw : |(2005521781/5000000000 : ℝ)|=(2005521781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1184677981/2500000000 : ℝ)|^8287 ≤ (37084574090659/100000000000000 : ℝ)^6239
        have hw : |(1184677981/2500000000 : ℝ)|=(1184677981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s2_4 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-434238523/2000000000 : ℝ)*x 0 + (5153582107/10000000000 : ℝ)*x 1 + (2758760681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434238523/2000000000 : ℝ)^8287 ≤ (1643896500083/12500000000000 : ℝ)^6239 := by
    have hnat : (434238523 : ℕ)^8287*12500000000000^6239 ≤ 1643896500083^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434238523 2000000000 1643896500083 12500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5153582107/10000000000 : ℝ)^8287 ≤ (20728927009301/50000000000000 : ℝ)^6239 := by
    have hnat : (5153582107 : ℕ)^8287*50000000000000^6239 ≤ 20728927009301^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153582107 10000000000 20728927009301 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2758760681/5000000000 : ℝ)^8287 ≤ (45390973972003/100000000000000 : ℝ)^6239 := by
    have hnat : (2758760681 : ℕ)^8287*100000000000000^6239 ≤ 45390973972003^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758760681 5000000000 45390973972003 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434238523/2000000000 : ℝ), (5153582107/10000000000 : ℝ), (2758760681/5000000000 : ℝ)] ![(1643896500083/12500000000000 : ℝ), (20728927009301/50000000000000 : ℝ), (45390973972003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434238523/2000000000 : ℝ)|^8287 ≤ (1643896500083/12500000000000 : ℝ)^6239
        have hw : |(-434238523/2000000000 : ℝ)|=(434238523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5153582107/10000000000 : ℝ)|^8287 ≤ (20728927009301/50000000000000 : ℝ)^6239
        have hw : |(5153582107/10000000000 : ℝ)|=(5153582107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2758760681/5000000000 : ℝ)|^8287 ≤ (45390973972003/100000000000000 : ℝ)^6239
        have hw : |(2758760681/5000000000 : ℝ)|=(2758760681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s2_5 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5282573461/10000000000 : ℝ)*x 0 + (-1996838137/10000000000 : ℝ)*x 1 + (5517521451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282573461/10000000000 : ℝ)^8287 ≤ (8568354920713/20000000000000 : ℝ)^6239 := by
    have hnat : (5282573461 : ℕ)^8287*20000000000000^6239 ≤ 8568354920713^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282573461 10000000000 8568354920713 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1996838137/10000000000 : ℝ)^8287 ≤ (11767250432893/100000000000000 : ℝ)^6239 := by
    have hnat : (1996838137 : ℕ)^8287*100000000000000^6239 ≤ 11767250432893^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996838137 10000000000 11767250432893 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5517521451/10000000000 : ℝ)^8287 ≤ (45390974944521/100000000000000 : ℝ)^6239 := by
    have hnat : (5517521451 : ℕ)^8287*100000000000000^6239 ≤ 45390974944521^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517521451 10000000000 45390974944521 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282573461/10000000000 : ℝ), (-1996838137/10000000000 : ℝ), (5517521451/10000000000 : ℝ)] ![(8568354920713/20000000000000 : ℝ), (11767250432893/100000000000000 : ℝ), (45390974944521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282573461/10000000000 : ℝ)|^8287 ≤ (8568354920713/20000000000000 : ℝ)^6239
        have hw : |(5282573461/10000000000 : ℝ)|=(5282573461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1996838137/10000000000 : ℝ)|^8287 ≤ (11767250432893/100000000000000 : ℝ)^6239
        have hw : |(-1996838137/10000000000 : ℝ)|=(1996838137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5517521451/10000000000 : ℝ)|^8287 ≤ (45390974944521/100000000000000 : ℝ)^6239
        have hw : |(5517521451/10000000000 : ℝ)|=(5517521451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s2_6 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5282573639/10000000000 : ℝ)*x 0 + (2758760687/5000000000 : ℝ)*x 1 + (-998419/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282573639/10000000000 : ℝ)^8287 ≤ (5355222065127/12500000000000 : ℝ)^6239 := by
    have hnat : (5282573639 : ℕ)^8287*12500000000000^6239 ≤ 5355222065127^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282573639 10000000000 5355222065127 12500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758760687/5000000000 : ℝ)^8287 ≤ (45390974103129/100000000000000 : ℝ)^6239 := by
    have hnat : (2758760687 : ℕ)^8287*100000000000000^6239 ≤ 45390974103129^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758760687 5000000000 45390974103129 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998419/5000000 : ℝ)^8287 ≤ (5883624680273/50000000000000 : ℝ)^6239 := by
    have hnat : (998419 : ℕ)^8287*50000000000000^6239 ≤ 5883624680273^6239*5000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998419 5000000 5883624680273 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282573639/10000000000 : ℝ), (2758760687/5000000000 : ℝ), (-998419/5000000 : ℝ)] ![(5355222065127/12500000000000 : ℝ), (45390974103129/100000000000000 : ℝ), (5883624680273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282573639/10000000000 : ℝ)|^8287 ≤ (5355222065127/12500000000000 : ℝ)^6239
        have hw : |(5282573639/10000000000 : ℝ)|=(5282573639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2758760687/5000000000 : ℝ)|^8287 ≤ (45390974103129/100000000000000 : ℝ)^6239
        have hw : |(2758760687/5000000000 : ℝ)|=(2758760687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-998419/5000000 : ℝ)|^8287 ≤ (5883624680273/50000000000000 : ℝ)^6239
        have hw : |(-998419/5000000 : ℝ)|=(998419/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s2_7 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174395853/400000000 : ℝ)*x 0 + (946704549/2000000000 : ℝ)*x 1 + (4016285109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174395853/400000000 : ℝ)^8287 ≤ (16599745459827/50000000000000 : ℝ)^6239 := by
    have hnat : (174395853 : ℕ)^8287*50000000000000^6239 ≤ 16599745459827^6239*400000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174395853 400000000 16599745459827 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (946704549/2000000000 : ℝ)^8287 ≤ (18515321704449/50000000000000 : ℝ)^6239 := by
    have hnat : (946704549 : ℕ)^8287*50000000000000^6239 ≤ 18515321704449^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946704549 2000000000 18515321704449 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4016285109/10000000000 : ℝ)^8287 ≤ (1860616603499/6250000000000 : ℝ)^6239 := by
    have hnat : (4016285109 : ℕ)^8287*6250000000000^6239 ≤ 1860616603499^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016285109 10000000000 1860616603499 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174395853/400000000 : ℝ), (946704549/2000000000 : ℝ), (4016285109/10000000000 : ℝ)] ![(16599745459827/50000000000000 : ℝ), (18515321704449/50000000000000 : ℝ), (1860616603499/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174395853/400000000 : ℝ)|^8287 ≤ (16599745459827/50000000000000 : ℝ)^6239
        have hw : |(174395853/400000000 : ℝ)|=(174395853/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(946704549/2000000000 : ℝ)|^8287 ≤ (18515321704449/50000000000000 : ℝ)^6239
        have hw : |(946704549/2000000000 : ℝ)|=(946704549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4016285109/10000000000 : ℝ)|^8287 ≤ (1860616603499/6250000000000 : ℝ)^6239
        have hw : |(4016285109/10000000000 : ℝ)|=(4016285109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1094_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10329/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8847/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (333/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10329/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10329/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10329/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10329/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10329/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10329/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5377/100000 : ℝ) ^ (4143/1024 : ℝ) ≤ (730960513698831/100000000000000000000 : ℝ) := by
    have hpowers : (5377/100000 : ℝ)^4143 ≤ (730960513698831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5377 : ℕ)^4143*100000000000000000000^1024 ≤ 730960513698831^1024*100000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5377 100000 730960513698831 100000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5377/100000 : ℝ)) (X := (730960513698831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10329/50000 : ℝ) ^ (4143/1024 : ℝ) ≤ (84700645210498203/50000000000000000000 : ℝ) := by
    have hpowers : (10329/50000 : ℝ)^4143 ≤ (84700645210498203/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10329 : ℕ)^4143*50000000000000000000^1024 ≤ 84700645210498203^1024*50000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10329 50000 84700645210498203 50000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10329/50000 : ℝ)) (X := (84700645210498203/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000730960513698831/50000000000000000000 : ℝ) ≤ (5000018066605047/5000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (50000730960513698831/50000000000000000000 : ℝ)^1024 ≤ (5000018066605047/5000000000000000 : ℝ)^4143 := by
      have hnat : (50000730960513698831 : ℕ)^1024*5000000000000000^4143 ≤ 5000018066605047^4143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000730960513698831 50000000000000000000 5000018066605047 5000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000018066605047/5000000000000000 : ℝ)) (X := (50000730960513698831/50000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100170132250934695237/100000000000000000000 : ℝ) ≤ (10004202364631709/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (100170132250934695237/100000000000000000000 : ℝ)^1024 ≤ (10004202364631709/10000000000000000 : ℝ)^4143 := by
      have hnat : (100170132250934695237 : ℕ)^1024*10000000000000000^4143 ≤ 10004202364631709^4143*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100170132250934695237 100000000000000000000 10004202364631709 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004202364631709/10000000000000000 : ℝ)) (X := (100170132250934695237/100000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25084700645210498203/25000000000000000000 : ℝ) ≤ (2502092149013331/2500000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (25084700645210498203/25000000000000000000 : ℝ)^1024 ≤ (2502092149013331/2500000000000000 : ℝ)^4143 := by
      have hnat : (25084700645210498203 : ℕ)^1024*2500000000000000^4143 ≤ 2502092149013331^4143*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25084700645210498203 25000000000000000000 2502092149013331 2500000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502092149013331/2500000000000000 : ℝ)) (X := (25084700645210498203/25000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(730960513698831/100000000000000000000 : ℝ) ≤ ((9547859281179712419/9550625000000000000 : ℝ)+2*(833246284323/305620000000000 : ℝ)*(5377/100000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (9547859281179712419/9550625000000000000 : ℝ)+2*(833246284323/305620000000000 : ℝ)*(5377/100000 : ℝ)=(5000018066605047/5000000000000000 : ℝ) by norm_num, show 1+2*(730960513698831/100000000000000000000 : ℝ)=(50000730960513698831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(84700645210498203/50000000000000000000 : ℝ)+(730960513698831/100000000000000000000 : ℝ) ≤ ((9547859281179712419/9550625000000000000 : ℝ)+(833246284323/305620000000000 : ℝ)*((10329/50000 : ℝ)+(5377/100000 : ℝ)))^(4143/1024 : ℝ) := by
    rw [show (9547859281179712419/9550625000000000000 : ℝ)+(833246284323/305620000000000 : ℝ)*((10329/50000 : ℝ)+(5377/100000 : ℝ))=(10004202364631709/10000000000000000 : ℝ) by norm_num, show 1+(84700645210498203/50000000000000000000 : ℝ)+(730960513698831/100000000000000000000 : ℝ)=(100170132250934695237/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(84700645210498203/50000000000000000000 : ℝ) ≤ ((9547859281179712419/9550625000000000000 : ℝ)+2*(833246284323/305620000000000 : ℝ)*(10329/50000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (9547859281179712419/9550625000000000000 : ℝ)+2*(833246284323/305620000000000 : ℝ)*(10329/50000 : ℝ)=(2502092149013331/2500000000000000 : ℝ) by norm_num, show 1+2*(84700645210498203/50000000000000000000 : ℝ)=(25084700645210498203/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9547859281179712419/9550625000000000000 : ℝ)*(X 1 0+X 2 0)+(833246284323/305620000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (5377/100000 : ℝ)) (hi := (10329/50000 : ℝ)) (c := (9547859281179712419/9550625000000000000 : ℝ)) (alpha := (833246284323/305620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9547859281179712419/9550625000000000000 : ℝ)*(X 0 1+X 2 1)+(833246284323/305620000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (5377/100000 : ℝ)) (hi := (10329/50000 : ℝ)) (c := (9547859281179712419/9550625000000000000 : ℝ)) (alpha := (833246284323/305620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9547859281179712419/9550625000000000000 : ℝ)*(X 0 2+X 1 2)+(833246284323/305620000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (5377/100000 : ℝ)) (hi := (10329/50000 : ℝ)) (c := (9547859281179712419/9550625000000000000 : ℝ)) (alpha := (833246284323/305620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1085538039/5000000000 : ℝ)*X 0 0+(5520181807/10000000000 : ℝ)*X 0 1+(5150948707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375953221/10000000000 : ℝ)*X 1 0+(-1181705129/5000000000 : ℝ)*X 1 1+(2575474877/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343988293/2500000000 : ℝ)*X 2 0+(5150949801/10000000000 : ℝ)*X 2 1+(-2363410261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359665319/10000000000 : ℝ)*X 0 0+(2005521781/5000000000 : ℝ)*X 0 1+(1184677981/2500000000 : ℝ)*X 0 2+(4359665319/10000000000 : ℝ)*X 1 0+(2005521781/5000000000 : ℝ)*X 1 1+(1184677981/2500000000 : ℝ)*X 1 2+(4359665319/10000000000 : ℝ)*X 2 0+(2005521781/5000000000 : ℝ)*X 2 1+(1184677981/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-434238523/2000000000 : ℝ)*X 0 0+(5153582107/10000000000 : ℝ)*X 0 1+(2758760681/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5282573461/10000000000 : ℝ)*X 1 0+(-1996838137/10000000000 : ℝ)*X 1 1+(5517521451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5282573639/10000000000 : ℝ)*X 2 0+(2758760687/5000000000 : ℝ)*X 2 1+(-998419/5000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174395853/400000000 : ℝ)*X 0 0+(946704549/2000000000 : ℝ)*X 0 1+(4016285109/10000000000 : ℝ)*X 0 2+(174395853/400000000 : ℝ)*X 1 0+(946704549/2000000000 : ℝ)*X 1 1+(4016285109/10000000000 : ℝ)*X 1 2+(174395853/400000000 : ℝ)*X 2 0+(946704549/2000000000 : ℝ)*X 2 1+(4016285109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5401704517688890759588483497/477531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1644186001/100000000000000 : ℝ)*(base19) + (1418841373/100000000000000 : ℝ)*(base23) + (276270779/100000000000000 : ℝ)*(upper3) + (107873253/100000000000000 : ℝ)*(upper4) + (114530867/100000000000000 : ℝ)*(upper5) + (2041317148069821/100000000000000 : ℝ)*(major0) + (2041317148069821/100000000000000 : ℝ)*(major1) + (2041317148069821/100000000000000 : ℝ)*(major2) + (108333585463817/4000000000000 : ℝ)*(sp0) + (1354179970410239/50000000000000 : ℝ)*(sp1) + (1354180083082553/50000000000000 : ℝ)*(sp2) + (687130777423859/50000000000000 : ℝ)*(sp3) + (10974205527/50000000000000 : ℝ)*(sp4) + (84212717/781250000000 : ℝ)*(sp7) + (687136167037747/50000000000000 : ℝ)*(f.failure) + (1354180792503239/50000000000000 : ℝ)*(f.sum) + (37705547533341/15281000000000000000000000000 : ℝ)*base65 + (7338270414425786751/955062500000000000000000000000000 : ℝ)*base68 + (1152213750028911751/955062500000000000000000000000000 : ℝ)*base70 + (1381092548263525749/955062500000000000000000000000000 : ℝ)*base71 + (1579927515511/15281000000000000000000000000 : ℝ)*base73 + (9771138405360724251/955062500000000000000000000000000 : ℝ)*base76 + (818029153706400749/955062500000000000000000000000000 : ℝ)*base77 + (5622978310550349251/955062500000000000000000000000000 : ℝ)*base80 + (28263135423833/15281000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5717361/5000000000000000000000 : ℝ)*base90 + (5717361/5000000000000000000000 : ℝ)*base92 + (5717361/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (578904906555018801730602333/95506250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149965657/12500000000000 : ℝ)*(base19) + (56466871/4000000000000 : ℝ)*(base23) + (21348977/12500000000000 : ℝ)*(upper3) + (38135491/100000000000000 : ℝ)*(lower4) + (115495741/100000000000000 : ℝ)*(upper5) + (414194919962381/20000000000000 : ℝ)*(major0) + (414194919962381/20000000000000 : ℝ)*(major1) + (414194919962381/20000000000000 : ℝ)*(major2) + (10678322493/100000000000000 : ℝ)*(sp1) + (3336692437/25000000000000 : ℝ)*(sp2) + (2747710429705379/100000000000000 : ℝ)*(sp4) + (274769855165763/10000000000000 : ℝ)*(sp5) + (171730979453991/6250000000000 : ℝ)*(sp6) + (697119283935301/50000000000000 : ℝ)*(sp7) + (697119283935301/50000000000000 : ℝ)*(f.failure) + (2747710429705379/100000000000000 : ℝ)*(f.sum) + (317872624189/305620000000000000000000000 : ℝ)*base66 + (450229018123190889/191012500000000000000000000000000 : ℝ)*base67 + (431499155466971611/191012500000000000000000000000000 : ℝ)*base70 + (669963595204184111/191012500000000000000000000000000 : ℝ)*base72 + (26591943285249/15281000000000000000000000000 : ℝ)*base73 + (411814985723353389/191012500000000000000000000000000 : ℝ)*base75 + (606558567268103389/191012500000000000000000000000000 : ℝ)*base77 + (826327905164953389/191012500000000000000000000000000 : ℝ)*base79 + (704076883491/611240000000000000000000000 : ℝ)*base82 + (4455863/5000000000000000000000 : ℝ)*base90 + (4455863/5000000000000000000000 : ℝ)*base92 + (4455863/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1094_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10329/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8847/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (333/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1094_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1094_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8847/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (333/2000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1094_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1094_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1094_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8847/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (333/2000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1094_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
