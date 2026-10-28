-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1188_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:52:17.069466+00:00
-- url     : https://prove2.me/submissions/d83c5cc7-8038-4271-a696-c5a9161444c7

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
theorem support_rectangle_w1188_s3_0 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141754677/10000000000 : ℝ)*x 0 + (5424605233/10000000000 : ℝ)*x 1 + (40907987/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141754677/10000000000 : ℝ)^8381 ≤ (6506094995287/50000000000000 : ℝ)^6333 := by
    have hnat : (2141754677 : ℕ)^8381*50000000000000^6333 ≤ 6506094995287^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141754677 10000000000 6506094995287 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424605233/10000000000 : ℝ)^8381 ≤ (22255464663221/50000000000000 : ℝ)^6333 := by
    have hnat : (5424605233 : ℕ)^8381*50000000000000^6333 ≤ 22255464663221^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424605233 10000000000 22255464663221 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40907987/78125000 : ℝ)^8381 ≤ (4247688066361/10000000000000 : ℝ)^6333 := by
    have hnat : (40907987 : ℕ)^8381*10000000000000^6333 ≤ 4247688066361^6333*78125000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40907987 78125000 4247688066361 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141754677/10000000000 : ℝ), (5424605233/10000000000 : ℝ), (40907987/78125000 : ℝ)] ![(6506094995287/50000000000000 : ℝ), (22255464663221/50000000000000 : ℝ), (4247688066361/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141754677/10000000000 : ℝ)|^8381 ≤ (6506094995287/50000000000000 : ℝ)^6333
        have hw : |(-2141754677/10000000000 : ℝ)|=(2141754677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424605233/10000000000 : ℝ)|^8381 ≤ (22255464663221/50000000000000 : ℝ)^6333
        have hw : |(5424605233/10000000000 : ℝ)|=(5424605233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40907987/78125000 : ℝ)|^8381 ≤ (4247688066361/10000000000000 : ℝ)^6333
        have hw : |(40907987/78125000 : ℝ)|=(40907987/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s3_1 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338177059/2500000000 : ℝ)*x 0 + (-2237956103/10000000000 : ℝ)*x 1 + (5236222493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338177059/2500000000 : ℝ)^8381 ≤ (43731886903189/100000000000000 : ℝ)^6333 := by
    have hnat : (1338177059 : ℕ)^8381*100000000000000^6333 ≤ 43731886903189^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338177059 2500000000 43731886903189 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237956103/10000000000 : ℝ)^8381 ≤ (13791230739943/100000000000000 : ℝ)^6333 := by
    have hnat : (2237956103 : ℕ)^8381*100000000000000^6333 ≤ 13791230739943^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237956103 10000000000 13791230739943 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236222493/10000000000 : ℝ)^8381 ≤ (42476882349079/100000000000000 : ℝ)^6333 := by
    have hnat : (5236222493 : ℕ)^8381*100000000000000^6333 ≤ 42476882349079^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236222493 10000000000 42476882349079 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338177059/2500000000 : ℝ), (-2237956103/10000000000 : ℝ), (5236222493/10000000000 : ℝ)] ![(43731886903189/100000000000000 : ℝ), (13791230739943/100000000000000 : ℝ), (42476882349079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338177059/2500000000 : ℝ)|^8381 ≤ (43731886903189/100000000000000 : ℝ)^6333
        have hw : |(1338177059/2500000000 : ℝ)|=(1338177059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2237956103/10000000000 : ℝ)|^8381 ≤ (13791230739943/100000000000000 : ℝ)^6333
        have hw : |(-2237956103/10000000000 : ℝ)|=(2237956103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236222493/10000000000 : ℝ)|^8381 ≤ (42476882349079/100000000000000 : ℝ)^6333
        have hw : |(5236222493/10000000000 : ℝ)|=(5236222493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s3_2 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (107054163/200000000 : ℝ)*x 0 + (1047244533/2000000000 : ℝ)*x 1 + (-223795599/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107054163/200000000 : ℝ)^8381 ≤ (21865942986673/50000000000000 : ℝ)^6333 := by
    have hnat : (107054163 : ℕ)^8381*50000000000000^6333 ≤ 21865942986673^6333*200000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107054163 200000000 21865942986673 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047244533/2000000000 : ℝ)^8381 ≤ (42476884195579/100000000000000 : ℝ)^6333 := by
    have hnat : (1047244533 : ℕ)^8381*100000000000000^6333 ≤ 42476884195579^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047244533 2000000000 42476884195579 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223795599/1000000000 : ℝ)^8381 ≤ (13791229818399/100000000000000 : ℝ)^6333 := by
    have hnat : (223795599 : ℕ)^8381*100000000000000^6333 ≤ 13791229818399^6333*1000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223795599 1000000000 13791229818399 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107054163/200000000 : ℝ), (1047244533/2000000000 : ℝ), (-223795599/1000000000 : ℝ)] ![(21865942986673/50000000000000 : ℝ), (42476884195579/100000000000000 : ℝ), (13791229818399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107054163/200000000 : ℝ)|^8381 ≤ (21865942986673/50000000000000 : ℝ)^6333
        have hw : |(107054163/200000000 : ℝ)|=(107054163/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047244533/2000000000 : ℝ)|^8381 ≤ (42476884195579/100000000000000 : ℝ)^6333
        have hw : |(1047244533/2000000000 : ℝ)|=(1047244533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223795599/1000000000 : ℝ)|^8381 ≤ (13791229818399/100000000000000 : ℝ)^6333
        have hw : |(-223795599/1000000000 : ℝ)|=(223795599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s3_3 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089062953/2500000000 : ℝ)*x 0 + (834240687/2000000000 : ℝ)*x 1 + (4549370393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089062953/2500000000 : ℝ)^8381 ≤ (33297173309031/100000000000000 : ℝ)^6333 := by
    have hnat : (1089062953 : ℕ)^8381*100000000000000^6333 ≤ 33297173309031^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089062953 2500000000 33297173309031 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834240687/2000000000 : ℝ)^8381 ≤ (31438327044497/100000000000000 : ℝ)^6333 := by
    have hnat : (834240687 : ℕ)^8381*100000000000000^6333 ≤ 31438327044497^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834240687 2000000000 31438327044497 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4549370393/10000000000 : ℝ)^8381 ≤ (17632249820317/50000000000000 : ℝ)^6333 := by
    have hnat : (4549370393 : ℕ)^8381*50000000000000^6333 ≤ 17632249820317^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549370393 10000000000 17632249820317 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089062953/2500000000 : ℝ), (834240687/2000000000 : ℝ), (4549370393/10000000000 : ℝ)] ![(33297173309031/100000000000000 : ℝ), (31438327044497/100000000000000 : ℝ), (17632249820317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089062953/2500000000 : ℝ)|^8381 ≤ (33297173309031/100000000000000 : ℝ)^6333
        have hw : |(1089062953/2500000000 : ℝ)|=(1089062953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834240687/2000000000 : ℝ)|^8381 ≤ (31438327044497/100000000000000 : ℝ)^6333
        have hw : |(834240687/2000000000 : ℝ)|=(834240687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4549370393/10000000000 : ℝ)|^8381 ≤ (17632249820317/50000000000000 : ℝ)^6333
        have hw : |(4549370393/10000000000 : ℝ)|=(4549370393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s3_4 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141770799/10000000000 : ℝ)*x 0 + (1309232767/2500000000 : ℝ)*x 1 + (5423892589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141770799/10000000000 : ℝ)^8381 ≤ (1626539951861/12500000000000 : ℝ)^6333 := by
    have hnat : (2141770799 : ℕ)^8381*12500000000000^6333 ≤ 1626539951861^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141770799 10000000000 1626539951861 12500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309232767/2500000000 : ℝ)^8381 ≤ (21242244699111/50000000000000 : ℝ)^6333 := by
    have hnat : (1309232767 : ℕ)^8381*50000000000000^6333 ≤ 21242244699111^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309232767 2500000000 21242244699111 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423892589/10000000000 : ℝ)^8381 ≤ (11125797744491/25000000000000 : ℝ)^6333 := by
    have hnat : (5423892589 : ℕ)^8381*25000000000000^6333 ≤ 11125797744491^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423892589 10000000000 11125797744491 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141770799/10000000000 : ℝ), (1309232767/2500000000 : ℝ), (5423892589/10000000000 : ℝ)] ![(1626539951861/12500000000000 : ℝ), (21242244699111/50000000000000 : ℝ), (11125797744491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141770799/10000000000 : ℝ)|^8381 ≤ (1626539951861/12500000000000 : ℝ)^6333
        have hw : |(-2141770799/10000000000 : ℝ)|=(2141770799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309232767/2500000000 : ℝ)|^8381 ≤ (21242244699111/50000000000000 : ℝ)^6333
        have hw : |(1309232767/2500000000 : ℝ)|=(1309232767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423892589/10000000000 : ℝ)|^8381 ≤ (11125797744491/25000000000000 : ℝ)^6333
        have hw : |(5423892589/10000000000 : ℝ)|=(5423892589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s3_5 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652412649/5000000000 : ℝ)*x 0 + (-2050285639/10000000000 : ℝ)*x 1 + (5423892527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652412649/5000000000 : ℝ)^8381 ≤ (8642984204357/20000000000000 : ℝ)^6333 := by
    have hnat : (2652412649 : ℕ)^8381*20000000000000^6333 ≤ 8642984204357^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652412649 5000000000 8642984204357 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050285639/10000000000 : ℝ)^8381 ≤ (12281888658709/100000000000000 : ℝ)^6333 := by
    have hnat : (2050285639 : ℕ)^8381*100000000000000^6333 ≤ 12281888658709^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050285639 10000000000 12281888658709 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423892527/10000000000 : ℝ)^8381 ≤ (22251595152371/50000000000000 : ℝ)^6333 := by
    have hnat : (5423892527 : ℕ)^8381*50000000000000^6333 ≤ 22251595152371^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423892527 10000000000 22251595152371 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652412649/5000000000 : ℝ), (-2050285639/10000000000 : ℝ), (5423892527/10000000000 : ℝ)] ![(8642984204357/20000000000000 : ℝ), (12281888658709/100000000000000 : ℝ), (22251595152371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652412649/5000000000 : ℝ)|^8381 ≤ (8642984204357/20000000000000 : ℝ)^6333
        have hw : |(2652412649/5000000000 : ℝ)|=(2652412649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050285639/10000000000 : ℝ)|^8381 ≤ (12281888658709/100000000000000 : ℝ)^6333
        have hw : |(-2050285639/10000000000 : ℝ)|=(2050285639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423892527/10000000000 : ℝ)|^8381 ≤ (22251595152371/50000000000000 : ℝ)^6333
        have hw : |(5423892527/10000000000 : ℝ)|=(5423892527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s3_6 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304824943/10000000000 : ℝ)*x 0 + (2711946457/5000000000 : ℝ)*x 1 + (-2050285591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304824943/10000000000 : ℝ)^8381 ≤ (43214917194619/100000000000000 : ℝ)^6333 := by
    have hnat : (5304824943 : ℕ)^8381*100000000000000^6333 ≤ 43214917194619^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304824943 10000000000 43214917194619 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711946457/5000000000 : ℝ)^8381 ≤ (44503194506949/100000000000000 : ℝ)^6333 := by
    have hnat : (2711946457 : ℕ)^8381*100000000000000^6333 ≤ 44503194506949^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711946457 5000000000 44503194506949 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050285591/10000000000 : ℝ)^8381 ≤ (3070472069547/25000000000000 : ℝ)^6333 := by
    have hnat : (2050285591 : ℕ)^8381*25000000000000^6333 ≤ 3070472069547^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050285591 10000000000 3070472069547 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304824943/10000000000 : ℝ), (2711946457/5000000000 : ℝ), (-2050285591/10000000000 : ℝ)] ![(43214917194619/100000000000000 : ℝ), (44503194506949/100000000000000 : ℝ), (3070472069547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304824943/10000000000 : ℝ)|^8381 ≤ (43214917194619/100000000000000 : ℝ)^6333
        have hw : |(5304824943/10000000000 : ℝ)|=(5304824943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711946457/5000000000 : ℝ)|^8381 ≤ (44503194506949/100000000000000 : ℝ)^6333
        have hw : |(2711946457/5000000000 : ℝ)|=(2711946457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2050285591/10000000000 : ℝ)|^8381 ≤ (3070472069547/25000000000000 : ℝ)^6333
        have hw : |(-2050285591/10000000000 : ℝ)|=(2050285591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s3_7 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356284407/10000000000 : ℝ)*x 0 + (454794737/1000000000 : ℝ)*x 1 + (3338107/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356284407/10000000000 : ℝ)^8381 ≤ (33297503019133/100000000000000 : ℝ)^6333 := by
    have hnat : (4356284407 : ℕ)^8381*100000000000000^6333 ≤ 33297503019133^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356284407 10000000000 33297503019133 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454794737/1000000000 : ℝ)^8381 ≤ (35249902670009/100000000000000 : ℝ)^6333 := by
    have hnat : (454794737 : ℕ)^8381*100000000000000^6333 ≤ 35249902670009^6333*1000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454794737 1000000000 35249902670009 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3338107/8000000 : ℝ)^8381 ≤ (6290518858291/20000000000000 : ℝ)^6333 := by
    have hnat : (3338107 : ℕ)^8381*20000000000000^6333 ≤ 6290518858291^6333*8000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3338107 8000000 6290518858291 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356284407/10000000000 : ℝ), (454794737/1000000000 : ℝ), (3338107/8000000 : ℝ)] ![(33297503019133/100000000000000 : ℝ), (35249902670009/100000000000000 : ℝ), (6290518858291/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356284407/10000000000 : ℝ)|^8381 ≤ (33297503019133/100000000000000 : ℝ)^6333
        have hw : |(4356284407/10000000000 : ℝ)|=(4356284407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(454794737/1000000000 : ℝ)|^8381 ≤ (35249902670009/100000000000000 : ℝ)^6333
        have hw : |(454794737/1000000000 : ℝ)|=(454794737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3338107/8000000 : ℝ)|^8381 ≤ (6290518858291/20000000000000 : ℝ)^6333
        have hw : |(3338107/8000000 : ℝ)|=(3338107/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1188_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10767/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7377/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9273/100000 : ℝ) ^ (2095/512 : ℝ) ≤ (5943949163714927/100000000000000000000 : ℝ) := by
    have hpowers : (9273/100000 : ℝ)^2095 ≤ (5943949163714927/100000000000000000000 : ℝ)^512 := by
      have hnat : (9273 : ℕ)^2095*100000000000000000000^512 ≤ 5943949163714927^512*100000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9273 100000 5943949163714927 100000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9273/100000 : ℝ)) (X := (5943949163714927/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16369/100000 : ℝ) ^ (2095/512 : ℝ) ≤ (30402429395256181/50000000000000000000 : ℝ) := by
    have hpowers : (16369/100000 : ℝ)^2095 ≤ (30402429395256181/50000000000000000000 : ℝ)^512 := by
      have hnat : (16369 : ℕ)^2095*50000000000000000000^512 ≤ 30402429395256181^512*100000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16369 100000 30402429395256181 50000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16369/100000 : ℝ)) (X := (30402429395256181/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005943949163714927/50000000000000000000 : ℝ) ≤ (1250036314621689/1250000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (50005943949163714927/50000000000000000000 : ℝ)^512 ≤ (1250036314621689/1250000000000000 : ℝ)^2095 := by
      have hnat : (50005943949163714927 : ℕ)^512*1250000000000000^2095 ≤ 1250036314621689^2095*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005943949163714927 50000000000000000000 1250036314621689 1250000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250036314621689/1250000000000000 : ℝ)) (X := (50005943949163714927/50000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100066748807954227289/100000000000000000000 : ℝ) ≤ (156275482379693/156250000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (100066748807954227289/100000000000000000000 : ℝ)^512 ≤ (156275482379693/156250000000000 : ℝ)^2095 := by
      have hnat : (100066748807954227289 : ℕ)^512*156250000000000^2095 ≤ 156275482379693^2095*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100066748807954227289 100000000000000000000 156275482379693 156250000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156275482379693/156250000000000 : ℝ)) (X := (100066748807954227289/100000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25030402429395256181/25000000000000000000 : ℝ) ≤ (1250371403453399/1250000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (25030402429395256181/25000000000000000000 : ℝ)^512 ≤ (1250371403453399/1250000000000000 : ℝ)^2095 := by
      have hnat : (25030402429395256181 : ℕ)^512*1250000000000000^2095 ≤ 1250371403453399^2095*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25030402429395256181 25000000000000000000 1250371403453399 1250000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250371403453399/1250000000000000 : ℝ)) (X := (25030402429395256181/25000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5943949163714927/100000000000000000000 : ℝ) ≤ ((4433575204909529157/4435000000000000000 : ℝ)+2*(33508883171/17740000000000 : ℝ)*(9273/100000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (4433575204909529157/4435000000000000000 : ℝ)+2*(33508883171/17740000000000 : ℝ)*(9273/100000 : ℝ)=(1250036314621689/1250000000000000 : ℝ) by norm_num, show 1+2*(5943949163714927/100000000000000000000 : ℝ)=(50005943949163714927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30402429395256181/50000000000000000000 : ℝ)+(5943949163714927/100000000000000000000 : ℝ) ≤ ((4433575204909529157/4435000000000000000 : ℝ)+(33508883171/17740000000000 : ℝ)*((16369/100000 : ℝ)+(9273/100000 : ℝ)))^(2095/512 : ℝ) := by
    rw [show (4433575204909529157/4435000000000000000 : ℝ)+(33508883171/17740000000000 : ℝ)*((16369/100000 : ℝ)+(9273/100000 : ℝ))=(156275482379693/156250000000000 : ℝ) by norm_num, show 1+(30402429395256181/50000000000000000000 : ℝ)+(5943949163714927/100000000000000000000 : ℝ)=(100066748807954227289/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30402429395256181/50000000000000000000 : ℝ) ≤ ((4433575204909529157/4435000000000000000 : ℝ)+2*(33508883171/17740000000000 : ℝ)*(16369/100000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (4433575204909529157/4435000000000000000 : ℝ)+2*(33508883171/17740000000000 : ℝ)*(16369/100000 : ℝ)=(1250371403453399/1250000000000000 : ℝ) by norm_num, show 1+2*(30402429395256181/50000000000000000000 : ℝ)=(25030402429395256181/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4433575204909529157/4435000000000000000 : ℝ)*(X 1 0+X 2 0)+(33508883171/17740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (9273/100000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (4433575204909529157/4435000000000000000 : ℝ)) (alpha := (33508883171/17740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4433575204909529157/4435000000000000000 : ℝ)*(X 0 1+X 2 1)+(33508883171/17740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (9273/100000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (4433575204909529157/4435000000000000000 : ℝ)) (alpha := (33508883171/17740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4433575204909529157/4435000000000000000 : ℝ)*(X 0 2+X 1 2)+(33508883171/17740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (9273/100000 : ℝ)) (hi := (16369/100000 : ℝ)) (c := (4433575204909529157/4435000000000000000 : ℝ)) (alpha := (33508883171/17740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2141754677/10000000000 : ℝ)*X 0 0+(5424605233/10000000000 : ℝ)*X 0 1+(40907987/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338177059/2500000000 : ℝ)*X 1 0+(-2237956103/10000000000 : ℝ)*X 1 1+(5236222493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((107054163/200000000 : ℝ)*X 2 0+(1047244533/2000000000 : ℝ)*X 2 1+(-223795599/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089062953/2500000000 : ℝ)*X 0 0+(834240687/2000000000 : ℝ)*X 0 1+(4549370393/10000000000 : ℝ)*X 0 2+(1089062953/2500000000 : ℝ)*X 1 0+(834240687/2000000000 : ℝ)*X 1 1+(4549370393/10000000000 : ℝ)*X 1 2+(1089062953/2500000000 : ℝ)*X 2 0+(834240687/2000000000 : ℝ)*X 2 1+(4549370393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2141770799/10000000000 : ℝ)*X 0 0+(1309232767/2500000000 : ℝ)*X 0 1+(5423892589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652412649/5000000000 : ℝ)*X 1 0+(-2050285639/10000000000 : ℝ)*X 1 1+(5423892527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304824943/10000000000 : ℝ)*X 2 0+(2711946457/5000000000 : ℝ)*X 2 1+(-2050285591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356284407/10000000000 : ℝ)*X 0 0+(454794737/1000000000 : ℝ)*X 0 1+(3338107/8000000 : ℝ)*X 0 2+(4356284407/10000000000 : ℝ)*X 1 0+(454794737/1000000000 : ℝ)*X 1 1+(3338107/8000000 : ℝ)*X 1 2+(4356284407/10000000000 : ℝ)*X 2 0+(454794737/1000000000 : ℝ)*X 2 1+(3338107/8000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (847977549179883333303617169/110875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1196722771/100000000000000 : ℝ)*(base19) + (962830291/100000000000000 : ℝ)*(base23) + (2485739/3125000000000 : ℝ)*(lower2) + (123693207/100000000000000 : ℝ)*(upper3) + (23518991/20000000000000 : ℝ)*(upper5) + (1988188143058387/50000000000000 : ℝ)*(major0) + (1988188143058387/50000000000000 : ℝ)*(major1) + (1988188143058387/50000000000000 : ℝ)*(major2) + (1327091197158071/25000000000000 : ℝ)*(sp0) + (132709795477857/2500000000000 : ℝ)*(sp1) + (5308392053006759/100000000000000 : ℝ)*(sp2) + (1322173379645139/50000000000000 : ℝ)*(sp3) + (28227204767/100000000000000 : ℝ)*(sp4) + (6271085601/50000000000000 : ℝ)*(sp7) + (66108982536537/2500000000000 : ℝ)*(f.failure) + (5308393015837051/100000000000000 : ℝ)*(f.sum) + (2995682635709/887000000000000000000000000 : ℝ)*base66 + (3769076747617639759/221750000000000000000000000000000 : ℝ)*base67 + (2752267193007389759/221750000000000000000000000000000 : ℝ)*base69 + (1259497841021639759/221750000000000000000000000000000 : ℝ)*base71 + (57459960471/13859375000000000000000000 : ℝ)*base73 + (4529541807854639759/221750000000000000000000000000000 : ℝ)*base75 + (788683614024139759/221750000000000000000000000000000 : ℝ)*base77 + (3974228891615389759/221750000000000000000000000000000 : ℝ)*base79 + (1422681592387/443500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (699389/62500000000000000000 : ℝ)*base90 + (699389/62500000000000000000 : ℝ)*base92 + (699389/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (591981599053565733993/88700000000000000000000000 : ℝ) := by norm_num
    linear_combination (965738213/50000000000000 : ℝ)*(base19) + (1843009413/100000000000000 : ℝ)*(base23) + (2026773/1562500000000 : ℝ)*(upper3) + (134345279/100000000000000 : ℝ)*(lower4) + (242302719/100000000000000 : ℝ)*(upper5) + (2003281992965179/50000000000000 : ℝ)*(major0) + (2003281992965179/50000000000000 : ℝ)*(major1) + (2003281992965179/50000000000000 : ℝ)*(major2) + (7683581511/20000000000000 : ℝ)*(sp1) + (20107183451/50000000000000 : ℝ)*(sp2) + (5348693103185339/100000000000000 : ℝ)*(sp4) + (2674326376900679/50000000000000 : ℝ)*(sp5) + (41786336295383/781250000000 : ℝ)*(sp6) + (1332217323104767/50000000000000 : ℝ)*(sp7) + (1332217323104767/50000000000000 : ℝ)*(f.failure) + (5348693103185339/100000000000000 : ℝ)*(f.sum) + (5008155442119/887000000000000000000000000 : ℝ)*base65 + (1781725954057525897/221750000000000000000000000000000 : ℝ)*base68 + (381958084169224103/221750000000000000000000000000000 : ℝ)*base69 + (1797191235894974103/221750000000000000000000000000000 : ℝ)*base71 + (757430423007/887000000000000000000000000 : ℝ)*base73 + (938831406151724103/221750000000000000000000000000000 : ℝ)*base75 + (516783156784025897/221750000000000000000000000000000 : ℝ)*base78 + (446320337137025897/221750000000000000000000000000000 : ℝ)*base80 + (622424367593/443500000000000000000000000 : ℝ)*base81 + (145301/1250000000000000000000 : ℝ)*base89 + (145301/1250000000000000000000 : ℝ)*base91 + (145301/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1188_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1188_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1188_s4_0 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144404771/10000000000 : ℝ)*x 0 + (5399776569/10000000000 : ℝ)*x 1 + (328707263/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144404771/10000000000 : ℝ)^8381 ≤ (6516750773289/50000000000000 : ℝ)^6333 := by
    have hnat : (2144404771 : ℕ)^8381*50000000000000^6333 ≤ 6516750773289^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144404771 10000000000 6516750773289 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399776569/10000000000 : ℝ)^8381 ≤ (11060379420137/25000000000000 : ℝ)^6333 := by
    have hnat : (5399776569 : ℕ)^8381*25000000000000^6333 ≤ 11060379420137^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399776569 10000000000 11060379420137 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328707263/625000000 : ℝ)^8381 ≤ (5340622595179/12500000000000 : ℝ)^6333 := by
    have hnat : (328707263 : ℕ)^8381*12500000000000^6333 ≤ 5340622595179^6333*625000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328707263 625000000 5340622595179 12500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144404771/10000000000 : ℝ), (5399776569/10000000000 : ℝ), (328707263/625000000 : ℝ)] ![(6516750773289/50000000000000 : ℝ), (11060379420137/25000000000000 : ℝ), (5340622595179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144404771/10000000000 : ℝ)|^8381 ≤ (6516750773289/50000000000000 : ℝ)^6333
        have hw : |(-2144404771/10000000000 : ℝ)|=(2144404771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399776569/10000000000 : ℝ)|^8381 ≤ (11060379420137/25000000000000 : ℝ)^6333
        have hw : |(5399776569/10000000000 : ℝ)|=(5399776569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328707263/625000000 : ℝ)|^8381 ≤ (5340622595179/12500000000000 : ℝ)^6333
        have hw : |(328707263/625000000 : ℝ)|=(328707263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s4_1 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673240449/5000000000 : ℝ)*x 0 + (-553938267/2500000000 : ℝ)*x 1 + (2629658107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673240449/5000000000 : ℝ)^8381 ≤ (10916142206213/25000000000000 : ℝ)^6333 := by
    have hnat : (2673240449 : ℕ)^8381*25000000000000^6333 ≤ 10916142206213^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673240449 5000000000 10916142206213 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553938267/2500000000 : ℝ)^8381 ≤ (680522516929/5000000000000 : ℝ)^6333 := by
    have hnat : (553938267 : ℕ)^8381*5000000000000^6333 ≤ 680522516929^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553938267 2500000000 680522516929 5000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629658107/5000000000 : ℝ)^8381 ≤ (2670311301621/6250000000000 : ℝ)^6333 := by
    have hnat : (2629658107 : ℕ)^8381*6250000000000^6333 ≤ 2670311301621^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629658107 5000000000 2670311301621 6250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673240449/5000000000 : ℝ), (-553938267/2500000000 : ℝ), (2629658107/5000000000 : ℝ)] ![(10916142206213/25000000000000 : ℝ), (680522516929/5000000000000 : ℝ), (2670311301621/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673240449/5000000000 : ℝ)|^8381 ≤ (10916142206213/25000000000000 : ℝ)^6333
        have hw : |(2673240449/5000000000 : ℝ)|=(2673240449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553938267/2500000000 : ℝ)|^8381 ≤ (680522516929/5000000000000 : ℝ)^6333
        have hw : |(-553938267/2500000000 : ℝ)|=(553938267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629658107/5000000000 : ℝ)|^8381 ≤ (2670311301621/6250000000000 : ℝ)^6333
        have hw : |(2629658107/5000000000 : ℝ)|=(2629658107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s4_2 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069296201/2000000000 : ℝ)*x 0 + (5259316181/10000000000 : ℝ)*x 1 + (-276969121/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069296201/2000000000 : ℝ)^8381 ≤ (21832284990657/50000000000000 : ℝ)^6333 := by
    have hnat : (1069296201 : ℕ)^8381*50000000000000^6333 ≤ 21832284990657^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069296201 2000000000 21832284990657 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259316181/10000000000 : ℝ)^8381 ≤ (42724980471161/100000000000000 : ℝ)^6333 := by
    have hnat : (5259316181 : ℕ)^8381*100000000000000^6333 ≤ 42724980471161^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259316181 10000000000 42724980471161 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276969121/1250000000 : ℝ)^8381 ≤ (13610449525679/100000000000000 : ℝ)^6333 := by
    have hnat : (276969121 : ℕ)^8381*100000000000000^6333 ≤ 13610449525679^6333*1250000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276969121 1250000000 13610449525679 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069296201/2000000000 : ℝ), (5259316181/10000000000 : ℝ), (-276969121/1250000000 : ℝ)] ![(21832284990657/50000000000000 : ℝ), (42724980471161/100000000000000 : ℝ), (13610449525679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069296201/2000000000 : ℝ)|^8381 ≤ (21832284990657/50000000000000 : ℝ)^6333
        have hw : |(1069296201/2000000000 : ℝ)|=(1069296201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259316181/10000000000 : ℝ)|^8381 ≤ (42724980471161/100000000000000 : ℝ)^6333
        have hw : |(5259316181/10000000000 : ℝ)|=(5259316181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276969121/1250000000 : ℝ)|^8381 ≤ (13610449525679/100000000000000 : ℝ)^6333
        have hw : |(-276969121/1250000000 : ℝ)|=(276969121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s4_3 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357838373/10000000000 : ℝ)*x 0 + (4219099761/10000000000 : ℝ)*x 1 + (4501065651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357838373/10000000000 : ℝ)^8381 ≤ (1332528914701/4000000000000 : ℝ)^6333 := by
    have hnat : (4357838373 : ℕ)^8381*4000000000000^6333 ≤ 1332528914701^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357838373 10000000000 1332528914701 4000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4219099761/10000000000 : ℝ)^8381 ≤ (3191694625157/10000000000000 : ℝ)^6333 := by
    have hnat : (4219099761 : ℕ)^8381*10000000000000^6333 ≤ 3191694625157^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219099761 10000000000 3191694625157 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501065651/10000000000 : ℝ)^8381 ≤ (8692457716009/25000000000000 : ℝ)^6333 := by
    have hnat : (4501065651 : ℕ)^8381*25000000000000^6333 ≤ 8692457716009^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501065651 10000000000 8692457716009 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357838373/10000000000 : ℝ), (4219099761/10000000000 : ℝ), (4501065651/10000000000 : ℝ)] ![(1332528914701/4000000000000 : ℝ), (3191694625157/10000000000000 : ℝ), (8692457716009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357838373/10000000000 : ℝ)|^8381 ≤ (1332528914701/4000000000000 : ℝ)^6333
        have hw : |(4357838373/10000000000 : ℝ)|=(4357838373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4219099761/10000000000 : ℝ)|^8381 ≤ (3191694625157/10000000000000 : ℝ)^6333
        have hw : |(4219099761/10000000000 : ℝ)|=(4219099761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501065651/10000000000 : ℝ)|^8381 ≤ (8692457716009/25000000000000 : ℝ)^6333
        have hw : |(4501065651/10000000000 : ℝ)|=(4501065651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s4_4 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144411599/10000000000 : ℝ)*x 0 + (5259710629/10000000000 : ℝ)*x 1 + (269969021/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144411599/10000000000 : ℝ)^8381 ≤ (13033556467071/100000000000000 : ℝ)^6333 := by
    have hnat : (2144411599 : ℕ)^8381*100000000000000^6333 ≤ 13033556467071^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144411599 10000000000 13033556467071 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259710629/10000000000 : ℝ)^8381 ≤ (213646105681/500000000000 : ℝ)^6333 := by
    have hnat : (5259710629 : ℕ)^8381*500000000000^6333 ≤ 213646105681^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259710629 10000000000 213646105681 500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269969021/500000000 : ℝ)^8381 ≤ (44237222375707/100000000000000 : ℝ)^6333 := by
    have hnat : (269969021 : ℕ)^8381*100000000000000^6333 ≤ 44237222375707^6333*500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269969021 500000000 44237222375707 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144411599/10000000000 : ℝ), (5259710629/10000000000 : ℝ), (269969021/500000000 : ℝ)] ![(13033556467071/100000000000000 : ℝ), (213646105681/500000000000 : ℝ), (44237222375707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144411599/10000000000 : ℝ)|^8381 ≤ (13033556467071/100000000000000 : ℝ)^6333
        have hw : |(-2144411599/10000000000 : ℝ)|=(2144411599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259710629/10000000000 : ℝ)|^8381 ≤ (213646105681/500000000000 : ℝ)^6333
        have hw : |(5259710629/10000000000 : ℝ)|=(5259710629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269969021/500000000 : ℝ)|^8381 ≤ (44237222375707/100000000000000 : ℝ)^6333
        have hw : |(269969021/500000000 : ℝ)|=(269969021/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s4_5 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310777463/10000000000 : ℝ)*x 0 + (-415137761/2000000000 : ℝ)*x 1 + (215975221/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310777463/10000000000 : ℝ)^8381 ≤ (5409887683207/12500000000000 : ℝ)^6333 := by
    have hnat : (5310777463 : ℕ)^8381*12500000000000^6333 ≤ 5409887683207^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310777463 10000000000 5409887683207 12500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415137761/2000000000 : ℝ)^8381 ≤ (1248367499669/10000000000000 : ℝ)^6333 := by
    have hnat : (415137761 : ℕ)^8381*10000000000000^6333 ≤ 1248367499669^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415137761 2000000000 1248367499669 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215975221/400000000 : ℝ)^8381 ≤ (11059305878543/25000000000000 : ℝ)^6333 := by
    have hnat : (215975221 : ℕ)^8381*25000000000000^6333 ≤ 11059305878543^6333*400000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215975221 400000000 11059305878543 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310777463/10000000000 : ℝ), (-415137761/2000000000 : ℝ), (215975221/400000000 : ℝ)] ![(5409887683207/12500000000000 : ℝ), (1248367499669/10000000000000 : ℝ), (11059305878543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310777463/10000000000 : ℝ)|^8381 ≤ (5409887683207/12500000000000 : ℝ)^6333
        have hw : |(5310777463/10000000000 : ℝ)|=(5310777463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415137761/2000000000 : ℝ)|^8381 ≤ (1248367499669/10000000000000 : ℝ)^6333
        have hw : |(-415137761/2000000000 : ℝ)|=(415137761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215975221/400000000 : ℝ)|^8381 ≤ (11059305878543/25000000000000 : ℝ)^6333
        have hw : |(215975221/400000000 : ℝ)|=(215975221/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s4_6 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310777783/10000000000 : ℝ)*x 0 + (2699690089/5000000000 : ℝ)*x 1 + (-518922211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310777783/10000000000 : ℝ)^8381 ≤ (10819776229187/25000000000000 : ℝ)^6333 := by
    have hnat : (5310777783 : ℕ)^8381*25000000000000^6333 ≤ 10819776229187^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310777783 10000000000 10819776229187 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699690089/5000000000 : ℝ)^8381 ≤ (44237219751817/100000000000000 : ℝ)^6333 := by
    have hnat : (2699690089 : ℕ)^8381*100000000000000^6333 ≤ 44237219751817^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699690089 5000000000 44237219751817 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518922211/2500000000 : ℝ)^8381 ≤ (12483675307097/100000000000000 : ℝ)^6333 := by
    have hnat : (518922211 : ℕ)^8381*100000000000000^6333 ≤ 12483675307097^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518922211 2500000000 12483675307097 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310777783/10000000000 : ℝ), (2699690089/5000000000 : ℝ), (-518922211/2500000000 : ℝ)] ![(10819776229187/25000000000000 : ℝ), (44237219751817/100000000000000 : ℝ), (12483675307097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310777783/10000000000 : ℝ)|^8381 ≤ (10819776229187/25000000000000 : ℝ)^6333
        have hw : |(5310777783/10000000000 : ℝ)|=(5310777783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699690089/5000000000 : ℝ)|^8381 ≤ (44237219751817/100000000000000 : ℝ)^6333
        have hw : |(2699690089/5000000000 : ℝ)|=(2699690089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-518922211/2500000000 : ℝ)|^8381 ≤ (12483675307097/100000000000000 : ℝ)^6333
        have hw : |(-518922211/2500000000 : ℝ)|=(518922211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s4_7 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357851667/10000000000 : ℝ)*x 0 + (225013669/500000000 : ℝ)*x 1 + (42198953/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357851667/10000000000 : ℝ)^8381 ≤ (33313357356837/100000000000000 : ℝ)^6333 := by
    have hnat : (4357851667 : ℕ)^8381*100000000000000^6333 ≤ 33313357356837^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357851667 10000000000 33313357356837 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225013669/500000000 : ℝ)^8381 ≤ (4345216474653/12500000000000 : ℝ)^6333 := by
    have hnat : (225013669 : ℕ)^8381*12500000000000^6333 ≤ 4345216474653^6333*500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225013669 500000000 4345216474653 12500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42198953/100000000 : ℝ)^8381 ≤ (31924910826559/100000000000000 : ℝ)^6333 := by
    have hnat : (42198953 : ℕ)^8381*100000000000000^6333 ≤ 31924910826559^6333*100000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42198953 100000000 31924910826559 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357851667/10000000000 : ℝ), (225013669/500000000 : ℝ), (42198953/100000000 : ℝ)] ![(33313357356837/100000000000000 : ℝ), (4345216474653/12500000000000 : ℝ), (31924910826559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357851667/10000000000 : ℝ)|^8381 ≤ (33313357356837/100000000000000 : ℝ)^6333
        have hw : |(4357851667/10000000000 : ℝ)|=(4357851667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225013669/500000000 : ℝ)|^8381 ≤ (4345216474653/12500000000000 : ℝ)^6333
        have hw : |(225013669/500000000 : ℝ)|=(225013669/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42198953/100000000 : ℝ)|^8381 ≤ (31924910826559/100000000000000 : ℝ)^6333
        have hw : |(42198953/100000000 : ℝ)|=(42198953/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1188_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (563/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10767/100000 : ℝ) ^ (2095/512 : ℝ) ≤ (10952876015718543/100000000000000000000 : ℝ) := by
    have hpowers : (10767/100000 : ℝ)^2095 ≤ (10952876015718543/100000000000000000000 : ℝ)^512 := by
      have hnat : (10767 : ℕ)^2095*100000000000000000000^512 ≤ 10952876015718543^512*100000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10767 100000 10952876015718543 100000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10767/100000 : ℝ)) (X := (10952876015718543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7377/50000 : ℝ) ^ (2095/512 : ℝ) ≤ (9937740226136923/25000000000000000000 : ℝ) := by
    have hpowers : (7377/50000 : ℝ)^2095 ≤ (9937740226136923/25000000000000000000 : ℝ)^512 := by
      have hnat : (7377 : ℕ)^2095*25000000000000000000^512 ≤ 9937740226136923^512*50000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7377 50000 9937740226136923 25000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7377/50000 : ℝ)) (X := (9937740226136923/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010952876015718543/50000000000000000000 : ℝ) ≤ (5000267656728741/5000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (50010952876015718543/50000000000000000000 : ℝ)^512 ≤ (5000267656728741/5000000000000000 : ℝ)^2095 := by
      have hnat : (50010952876015718543 : ℕ)^512*5000000000000000^2095 ≤ 5000267656728741^2095*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010952876015718543 50000000000000000000 5000267656728741 5000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000267656728741/5000000000000000 : ℝ)) (X := (50010952876015718543/50000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010140767384053247/20000000000000000000 : ℝ) ≤ (500061946045293/500000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (20010140767384053247/20000000000000000000 : ℝ)^512 ≤ (500061946045293/500000000000000 : ℝ)^2095 := by
      have hnat : (20010140767384053247 : ℕ)^512*500000000000000^2095 ≤ 500061946045293^2095*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010140767384053247 20000000000000000000 500061946045293 500000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500061946045293/500000000000000 : ℝ)) (X := (20010140767384053247/20000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509937740226136923/12500000000000000000 : ℝ) ≤ (5000971264177119/5000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (12509937740226136923/12500000000000000000 : ℝ)^512 ≤ (5000971264177119/5000000000000000 : ℝ)^2095 := by
      have hnat : (12509937740226136923 : ℕ)^512*5000000000000000^2095 ≤ 5000971264177119^2095*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509937740226136923 12500000000000000000 5000971264177119 5000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000971264177119/5000000000000000 : ℝ)) (X := (12509937740226136923/12500000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10952876015718543/100000000000000000000 : ℝ) ≤ ((2214276822886756049/2215000000000000000 : ℝ)+2*(117267908063/66450000000000 : ℝ)*(10767/100000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (2214276822886756049/2215000000000000000 : ℝ)+2*(117267908063/66450000000000 : ℝ)*(10767/100000 : ℝ)=(5000267656728741/5000000000000000 : ℝ) by norm_num, show 1+2*(10952876015718543/100000000000000000000 : ℝ)=(50010952876015718543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9937740226136923/25000000000000000000 : ℝ)+(10952876015718543/100000000000000000000 : ℝ) ≤ ((2214276822886756049/2215000000000000000 : ℝ)+(117267908063/66450000000000 : ℝ)*((7377/50000 : ℝ)+(10767/100000 : ℝ)))^(2095/512 : ℝ) := by
    rw [show (2214276822886756049/2215000000000000000 : ℝ)+(117267908063/66450000000000 : ℝ)*((7377/50000 : ℝ)+(10767/100000 : ℝ))=(500061946045293/500000000000000 : ℝ) by norm_num, show 1+(9937740226136923/25000000000000000000 : ℝ)+(10952876015718543/100000000000000000000 : ℝ)=(20010140767384053247/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9937740226136923/25000000000000000000 : ℝ) ≤ ((2214276822886756049/2215000000000000000 : ℝ)+2*(117267908063/66450000000000 : ℝ)*(7377/50000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (2214276822886756049/2215000000000000000 : ℝ)+2*(117267908063/66450000000000 : ℝ)*(7377/50000 : ℝ)=(5000971264177119/5000000000000000 : ℝ) by norm_num, show 1+2*(9937740226136923/25000000000000000000 : ℝ)=(12509937740226136923/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2214276822886756049/2215000000000000000 : ℝ)*(X 1 0+X 2 0)+(117267908063/66450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (10767/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (2214276822886756049/2215000000000000000 : ℝ)) (alpha := (117267908063/66450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2214276822886756049/2215000000000000000 : ℝ)*(X 0 1+X 2 1)+(117267908063/66450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (10767/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (2214276822886756049/2215000000000000000 : ℝ)) (alpha := (117267908063/66450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2214276822886756049/2215000000000000000 : ℝ)*(X 0 2+X 1 2)+(117267908063/66450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (10767/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (2214276822886756049/2215000000000000000 : ℝ)) (alpha := (117267908063/66450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2144404771/10000000000 : ℝ)*X 0 0+(5399776569/10000000000 : ℝ)*X 0 1+(328707263/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673240449/5000000000 : ℝ)*X 1 0+(-553938267/2500000000 : ℝ)*X 1 1+(2629658107/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069296201/2000000000 : ℝ)*X 2 0+(5259316181/10000000000 : ℝ)*X 2 1+(-276969121/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357838373/10000000000 : ℝ)*X 0 0+(4219099761/10000000000 : ℝ)*X 0 1+(4501065651/10000000000 : ℝ)*X 0 2+(4357838373/10000000000 : ℝ)*X 1 0+(4219099761/10000000000 : ℝ)*X 1 1+(4501065651/10000000000 : ℝ)*X 1 2+(4357838373/10000000000 : ℝ)*X 2 0+(4219099761/10000000000 : ℝ)*X 2 1+(4501065651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2144411599/10000000000 : ℝ)*X 0 0+(5259710629/10000000000 : ℝ)*X 0 1+(269969021/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310777463/10000000000 : ℝ)*X 1 0+(-415137761/2000000000 : ℝ)*X 1 1+(215975221/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310777783/10000000000 : ℝ)*X 2 0+(2699690089/5000000000 : ℝ)*X 2 1+(-518922211/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357851667/10000000000 : ℝ)*X 0 0+(225013669/500000000 : ℝ)*X 0 1+(42198953/100000000 : ℝ)*X 0 2+(4357851667/10000000000 : ℝ)*X 1 0+(225013669/500000000 : ℝ)*X 1 1+(42198953/100000000 : ℝ)*X 1 2+(4357851667/10000000000 : ℝ)*X 2 0+(225013669/500000000 : ℝ)*X 2 1+(42198953/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8884529552587650767492679/2215000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (833124727/100000000000000 : ℝ)*(base19) + (908217741/100000000000000 : ℝ)*(base23) + (36030181/100000000000000 : ℝ)*(lower2) + (24155161/50000000000000 : ℝ)*(upper3) + (170096583/100000000000000 : ℝ)*(upper5) + (106660393218681/2000000000000 : ℝ)*(major0) + (106660393218681/2000000000000 : ℝ)*(major1) + (106660393218681/2000000000000 : ℝ)*(major2) + (1779865855711499/25000000000000 : ℝ)*(sp0) + (7119487643905853/100000000000000 : ℝ)*(sp1) + (7119487568812839/100000000000000 : ℝ)*(sp2) + (1773270031273697/50000000000000 : ℝ)*(sp3) + (5010836917/20000000000000 : ℝ)*(sp4) + (10648587633/100000000000000 : ℝ)*(sp7) + (886637677783757/25000000000000 : ℝ)*(f.failure) + (355974423851529/5000000000000 : ℝ)*(f.sum) + (161387805993/221500000000000000000000000 : ℝ)*base66 + (62555009787561369/4430000000000000000000000000000 : ℝ)*base67 + (56269667315991369/4430000000000000000000000000000 : ℝ)*base69 + (26549847646841369/4430000000000000000000000000000 : ℝ)*base71 + (14045432289/44300000000000000000000000 : ℝ)*base74 + (191797225800171369/4430000000000000000000000000000 : ℝ)*base75 + (48971286146411369/4430000000000000000000000000000 : ℝ)*base77 + (133592158854461369/4430000000000000000000000000000 : ℝ)*base79 + (62394441407/221500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2247729/625000000000000000000 : ℝ)*base90 + (2247729/625000000000000000000 : ℝ)*base92 + (2247729/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62859145334968534034346399/55375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (389744037/100000000000000 : ℝ)*(base19) + (42521677/4000000000000 : ℝ)*(base23) + (13171219/10000000000000 : ℝ)*(upper2) + (42047413/20000000000000 : ℝ)*(upper5) + (5363182571269283/100000000000000 : ℝ)*(major0) + (5363182571269283/100000000000000 : ℝ)*(major1) + (5363182571269283/100000000000000 : ℝ)*(major2) + (704606139/100000000000000 : ℝ)*(sp0) + (9436838043/50000000000000 : ℝ)*(sp1) + (3592656077/20000000000000 : ℝ)*(sp2) + (7159754829644579/100000000000000 : ℝ)*(sp4) + (7159736270830597/100000000000000 : ℝ)*(sp5) + (7159736507928409/100000000000000 : ℝ)*(sp6) + (5706575312719/160000000000 : ℝ)*(sp7) + (5706575312719/160000000000 : ℝ)*(f.failure) + (7159755534250719/100000000000000 : ℝ)*(f.sum) + (11081045395583/6645000000000000000000000000 : ℝ)*base65 + (1115786834168328601/664500000000000000000000000000000 : ℝ)*base67 + (4284284433923328601/664500000000000000000000000000000 : ℝ)*base69 + (6145205273129328601/664500000000000000000000000000000 : ℝ)*base71 + (17710024742557/6645000000000000000000000000 : ℝ)*base74 + (5941731142313171399/664500000000000000000000000000000 : ℝ)*base76 + (8745736965450828601/664500000000000000000000000000000 : ℝ)*base77 + (9180292262445828601/664500000000000000000000000000000 : ℝ)*base79 + (5945075318089/3322500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (14843/4000000000000000000 : ℝ)*base90 + (14843/4000000000000000000 : ℝ)*base92 + (14843/4000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1188_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1188_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1188_s5_0 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144948597/10000000000 : ℝ)*x 0 + (5393731293/10000000000 : ℝ)*x 1 + (5265004239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144948597/10000000000 : ℝ)^8381 ≤ (6518937973173/50000000000000 : ℝ)^6333 := by
    have hnat : (2144948597 : ℕ)^8381*50000000000000^6333 ≤ 6518937973173^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144948597 10000000000 6518937973173 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393731293/10000000000 : ℝ)^8381 ≤ (22087990980719/50000000000000 : ℝ)^6333 := by
    have hnat : (5393731293 : ℕ)^8381*50000000000000^6333 ≤ 22087990980719^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393731293 10000000000 22087990980719 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265004239/10000000000 : ℝ)^8381 ≤ (21393071038719/50000000000000 : ℝ)^6333 := by
    have hnat : (5265004239 : ℕ)^8381*50000000000000^6333 ≤ 21393071038719^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265004239 10000000000 21393071038719 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144948597/10000000000 : ℝ), (5393731293/10000000000 : ℝ), (5265004239/10000000000 : ℝ)] ![(6518937973173/50000000000000 : ℝ), (22087990980719/50000000000000 : ℝ), (21393071038719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144948597/10000000000 : ℝ)|^8381 ≤ (6518937973173/50000000000000 : ℝ)^6333
        have hw : |(-2144948597/10000000000 : ℝ)|=(2144948597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393731293/10000000000 : ℝ)|^8381 ≤ (22087990980719/50000000000000 : ℝ)^6333
        have hw : |(5393731293/10000000000 : ℝ)|=(5393731293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265004239/10000000000 : ℝ)|^8381 ≤ (21393071038719/50000000000000 : ℝ)^6333
        have hw : |(5265004239/10000000000 : ℝ)|=(5265004239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s5_1 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336239567/2500000000 : ℝ)*x 0 + (-1105125671/5000000000 : ℝ)*x 1 + (5265004263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336239567/2500000000 : ℝ)^8381 ≤ (10912028228831/25000000000000 : ℝ)^6333 := by
    have hnat : (1336239567 : ℕ)^8381*25000000000000^6333 ≤ 10912028228831^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336239567 2500000000 10912028228831 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105125671/5000000000 : ℝ)^8381 ≤ (13565744736193/100000000000000 : ℝ)^6333 := by
    have hnat : (1105125671 : ℕ)^8381*100000000000000^6333 ≤ 13565744736193^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105125671 5000000000 13565744736193 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265004263/10000000000 : ℝ)^8381 ≤ (42786142335547/100000000000000 : ℝ)^6333 := by
    have hnat : (5265004263 : ℕ)^8381*100000000000000^6333 ≤ 42786142335547^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265004263 10000000000 42786142335547 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336239567/2500000000 : ℝ), (-1105125671/5000000000 : ℝ), (5265004263/10000000000 : ℝ)] ![(10912028228831/25000000000000 : ℝ), (13565744736193/100000000000000 : ℝ), (42786142335547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336239567/2500000000 : ℝ)|^8381 ≤ (10912028228831/25000000000000 : ℝ)^6333
        have hw : |(1336239567/2500000000 : ℝ)|=(1336239567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1105125671/5000000000 : ℝ)|^8381 ≤ (13565744736193/100000000000000 : ℝ)^6333
        have hw : |(-1105125671/5000000000 : ℝ)|=(1105125671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265004263/10000000000 : ℝ)|^8381 ≤ (42786142335547/100000000000000 : ℝ)^6333
        have hw : |(5265004263/10000000000 : ℝ)|=(5265004263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s5_2 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068991663/2000000000 : ℝ)*x 0 + (2632502129/5000000000 : ℝ)*x 1 + (-1105125643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068991663/2000000000 : ℝ)^8381 ≤ (8729622684651/20000000000000 : ℝ)^6333 := by
    have hnat : (1068991663 : ℕ)^8381*20000000000000^6333 ≤ 8729622684651^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068991663 2000000000 8729622684651 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632502129/5000000000 : ℝ)^8381 ≤ (21393071140887/50000000000000 : ℝ)^6333 := by
    have hnat : (2632502129 : ℕ)^8381*50000000000000^6333 ≤ 21393071140887^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632502129 5000000000 21393071140887 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105125643/5000000000 : ℝ)^8381 ≤ (6782872140667/50000000000000 : ℝ)^6333 := by
    have hnat : (1105125643 : ℕ)^8381*50000000000000^6333 ≤ 6782872140667^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105125643 5000000000 6782872140667 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068991663/2000000000 : ℝ), (2632502129/5000000000 : ℝ), (-1105125643/5000000000 : ℝ)] ![(8729622684651/20000000000000 : ℝ), (21393071140887/50000000000000 : ℝ), (6782872140667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068991663/2000000000 : ℝ)|^8381 ≤ (8729622684651/20000000000000 : ℝ)^6333
        have hw : |(1068991663/2000000000 : ℝ)|=(1068991663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632502129/5000000000 : ℝ)|^8381 ≤ (21393071140887/50000000000000 : ℝ)^6333
        have hw : |(2632502129/5000000000 : ℝ)|=(2632502129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1105125643/5000000000 : ℝ)|^8381 ≤ (6782872140667/50000000000000 : ℝ)^6333
        have hw : |(-1105125643/5000000000 : ℝ)|=(1105125643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s5_3 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358156357/10000000000 : ℝ)*x 0 + (4230835839/10000000000 : ℝ)*x 1 + (4489247683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358156357/10000000000 : ℝ)^8381 ≤ (33316439802453/100000000000000 : ℝ)^6333 := by
    have hnat : (4358156357 : ℕ)^8381*100000000000000^6333 ≤ 33316439802453^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358156357 10000000000 33316439802453 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230835839/10000000000 : ℝ)^8381 ≤ (16017245880903/50000000000000 : ℝ)^6333 := by
    have hnat : (4230835839 : ℕ)^8381*50000000000000^6333 ≤ 16017245880903^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230835839 10000000000 16017245880903 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489247683/10000000000 : ℝ)^8381 ≤ (34649068426811/100000000000000 : ℝ)^6333 := by
    have hnat : (4489247683 : ℕ)^8381*100000000000000^6333 ≤ 34649068426811^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489247683 10000000000 34649068426811 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358156357/10000000000 : ℝ), (4230835839/10000000000 : ℝ), (4489247683/10000000000 : ℝ)] ![(33316439802453/100000000000000 : ℝ), (16017245880903/50000000000000 : ℝ), (34649068426811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358156357/10000000000 : ℝ)|^8381 ≤ (33316439802453/100000000000000 : ℝ)^6333
        have hw : |(4358156357/10000000000 : ℝ)|=(4358156357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230835839/10000000000 : ℝ)|^8381 ≤ (16017245880903/50000000000000 : ℝ)^6333
        have hw : |(4230835839/10000000000 : ℝ)|=(4230835839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489247683/10000000000 : ℝ)|^8381 ≤ (34649068426811/100000000000000 : ℝ)^6333
        have hw : |(4489247683/10000000000 : ℝ)|=(4489247683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s5_4 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-536238427/2500000000 : ℝ)*x 0 + (1053067169/2000000000 : ℝ)*x 1 + (1348349617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536238427/2500000000 : ℝ)^8381 ≤ (203717454057/1562500000000 : ℝ)^6333 := by
    have hnat : (536238427 : ℕ)^8381*1562500000000^6333 ≤ 203717454057^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536238427 2500000000 203717454057 1562500000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053067169/2000000000 : ℝ)^8381 ≤ (5348713546857/12500000000000 : ℝ)^6333 := by
    have hnat : (1053067169 : ℕ)^8381*12500000000000^6333 ≤ 5348713546857^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053067169 2000000000 5348713546857 12500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348349617/2500000000 : ℝ)^8381 ≤ (44172374556751/100000000000000 : ℝ)^6333 := by
    have hnat : (1348349617 : ℕ)^8381*100000000000000^6333 ≤ 44172374556751^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348349617 2500000000 44172374556751 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-536238427/2500000000 : ℝ), (1053067169/2000000000 : ℝ), (1348349617/2500000000 : ℝ)] ![(203717454057/1562500000000 : ℝ), (5348713546857/12500000000000 : ℝ), (44172374556751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-536238427/2500000000 : ℝ)|^8381 ≤ (203717454057/1562500000000 : ℝ)^6333
        have hw : |(-536238427/2500000000 : ℝ)|=(536238427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053067169/2000000000 : ℝ)|^8381 ≤ (5348713546857/12500000000000 : ℝ)^6333
        have hw : |(1053067169/2000000000 : ℝ)|=(1053067169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348349617/2500000000 : ℝ)|^8381 ≤ (44172374556751/100000000000000 : ℝ)^6333
        have hw : |(1348349617/2500000000 : ℝ)|=(1348349617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s5_5 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328059021/2500000000 : ℝ)*x 0 + (-1040928559/5000000000 : ℝ)*x 1 + (337087401/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328059021/2500000000 : ℝ)^8381 ≤ (21647416448363/50000000000000 : ℝ)^6333 := by
    have hnat : (1328059021 : ℕ)^8381*50000000000000^6333 ≤ 21647416448363^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328059021 2500000000 21647416448363 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040928559/5000000000 : ℝ)^8381 ≤ (783299567813/6250000000000 : ℝ)^6333 := by
    have hnat : (1040928559 : ℕ)^8381*6250000000000^6333 ≤ 783299567813^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040928559 5000000000 783299567813 6250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337087401/625000000 : ℝ)^8381 ≤ (22086186996571/50000000000000 : ℝ)^6333 := by
    have hnat : (337087401 : ℕ)^8381*50000000000000^6333 ≤ 22086186996571^6333*625000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337087401 625000000 22086186996571 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328059021/2500000000 : ℝ), (-1040928559/5000000000 : ℝ), (337087401/625000000 : ℝ)] ![(21647416448363/50000000000000 : ℝ), (783299567813/6250000000000 : ℝ), (22086186996571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328059021/2500000000 : ℝ)|^8381 ≤ (21647416448363/50000000000000 : ℝ)^6333
        have hw : |(1328059021/2500000000 : ℝ)|=(1328059021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040928559/5000000000 : ℝ)|^8381 ≤ (783299567813/6250000000000 : ℝ)^6333
        have hw : |(-1040928559/5000000000 : ℝ)|=(1040928559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337087401/625000000 : ℝ)|^8381 ≤ (22086186996571/50000000000000 : ℝ)^6333
        have hw : |(337087401/625000000 : ℝ)|=(337087401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s5_6 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212489443/400000000 : ℝ)*x 0 + (5393398433/10000000000 : ℝ)*x 1 + (-520464277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212489443/400000000 : ℝ)^8381 ≤ (8658966559931/20000000000000 : ℝ)^6333 := by
    have hnat : (212489443 : ℕ)^8381*20000000000000^6333 ≤ 8658966559931^6333*400000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212489443 400000000 8658966559931 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393398433/10000000000 : ℝ)^8381 ≤ (44172374177399/100000000000000 : ℝ)^6333 := by
    have hnat : (5393398433 : ℕ)^8381*100000000000000^6333 ≤ 44172374177399^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393398433 10000000000 44172374177399 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520464277/2500000000 : ℝ)^8381 ≤ (626639650267/5000000000000 : ℝ)^6333 := by
    have hnat : (520464277 : ℕ)^8381*5000000000000^6333 ≤ 626639650267^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520464277 2500000000 626639650267 5000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212489443/400000000 : ℝ), (5393398433/10000000000 : ℝ), (-520464277/2500000000 : ℝ)] ![(8658966559931/20000000000000 : ℝ), (44172374177399/100000000000000 : ℝ), (626639650267/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212489443/400000000 : ℝ)|^8381 ≤ (8658966559931/20000000000000 : ℝ)^6333
        have hw : |(212489443/400000000 : ℝ)|=(212489443/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393398433/10000000000 : ℝ)|^8381 ≤ (44172374177399/100000000000000 : ℝ)^6333
        have hw : |(5393398433/10000000000 : ℝ)|=(5393398433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520464277/2500000000 : ℝ)|^8381 ≤ (626639650267/5000000000000 : ℝ)^6333
        have hw : |(-520464277/2500000000 : ℝ)|=(520464277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s5_7 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089541651/2500000000 : ℝ)*x 0 + (4488582041/10000000000 : ℝ)*x 1 + (4231503987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089541651/2500000000 : ℝ)^8381 ≤ (4164567933637/12500000000000 : ℝ)^6333 := by
    have hnat : (1089541651 : ℕ)^8381*12500000000000^6333 ≤ 4164567933637^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089541651 2500000000 4164567933637 12500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488582041/10000000000 : ℝ)^8381 ≤ (34642269589449/100000000000000 : ℝ)^6333 := by
    have hnat : (4488582041 : ℕ)^8381*100000000000000^6333 ≤ 34642269589449^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488582041 10000000000 34642269589449 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231503987/10000000000 : ℝ)^8381 ≤ (2002574183401/6250000000000 : ℝ)^6333 := by
    have hnat : (4231503987 : ℕ)^8381*6250000000000^6333 ≤ 2002574183401^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231503987 10000000000 2002574183401 6250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089541651/2500000000 : ℝ), (4488582041/10000000000 : ℝ), (4231503987/10000000000 : ℝ)] ![(4164567933637/12500000000000 : ℝ), (34642269589449/100000000000000 : ℝ), (2002574183401/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089541651/2500000000 : ℝ)|^8381 ≤ (4164567933637/12500000000000 : ℝ)^6333
        have hw : |(1089541651/2500000000 : ℝ)|=(1089541651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488582041/10000000000 : ℝ)|^8381 ≤ (34642269589449/100000000000000 : ℝ)^6333
        have hw : |(4488582041/10000000000 : ℝ)|=(4488582041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231503987/10000000000 : ℝ)|^8381 ≤ (2002574183401/6250000000000 : ℝ)^6333
        have hw : |(4231503987/10000000000 : ℝ)|=(4231503987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1188_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11381/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3527/25000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (563/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (563/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (563/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (563/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (563/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (563/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (563/5000 : ℝ) ^ (2095/512 : ℝ) ≤ (13154906034076969/100000000000000000000 : ℝ) := by
    have hpowers : (563/5000 : ℝ)^2095 ≤ (13154906034076969/100000000000000000000 : ℝ)^512 := by
      have hnat : (563 : ℕ)^2095*100000000000000000000^512 ≤ 13154906034076969^512*5000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 5000 13154906034076969 100000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/5000 : ℝ)) (X := (13154906034076969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (2095/512 : ℝ) ≤ (17161526339674281/50000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^2095 ≤ (17161526339674281/50000000000000000000 : ℝ)^512 := by
      have hnat : (7117 : ℕ)^2095*50000000000000000000^512 ≤ 17161526339674281^512*50000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 17161526339674281 50000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (17161526339674281/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013154906034076969/50000000000000000000 : ℝ) ≤ (5000321462649413/5000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (50013154906034076969/50000000000000000000 : ℝ)^512 ≤ (5000321462649413/5000000000000000 : ℝ)^2095 := by
      have hnat : (50013154906034076969 : ℕ)^512*5000000000000000^2095 ≤ 5000321462649413^2095*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013154906034076969 50000000000000000000 5000321462649413 5000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000321462649413/5000000000000000 : ℝ)) (X := (50013154906034076969/50000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047477958713425531/100000000000000000000 : ℝ) ≤ (39067031689239/39062500000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (100047477958713425531/100000000000000000000 : ℝ)^512 ≤ (39067031689239/39062500000000 : ℝ)^2095 := by
      have hnat : (100047477958713425531 : ℕ)^512*39062500000000^2095 ≤ 39067031689239^2095*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047477958713425531 100000000000000000000 39067031689239 39062500000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39067031689239/39062500000000 : ℝ)) (X := (100047477958713425531/100000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017161526339674281/25000000000000000000 : ℝ) ≤ (5000838649795771/5000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (25017161526339674281/25000000000000000000 : ℝ)^512 ≤ (5000838649795771/5000000000000000 : ℝ)^2095 := by
      have hnat : (25017161526339674281 : ℕ)^512*5000000000000000^2095 ≤ 5000838649795771^2095*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017161526339674281 25000000000000000000 5000838649795771 5000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000838649795771/5000000000000000 : ℝ)) (X := (25017161526339674281/25000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13154906034076969/100000000000000000000 : ℝ) ≤ ((7432566251325681591/7435000000000000000 : ℝ)+2*(258593573179/148700000000000 : ℝ)*(563/5000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (7432566251325681591/7435000000000000000 : ℝ)+2*(258593573179/148700000000000 : ℝ)*(563/5000 : ℝ)=(5000321462649413/5000000000000000 : ℝ) by norm_num, show 1+2*(13154906034076969/100000000000000000000 : ℝ)=(50013154906034076969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17161526339674281/50000000000000000000 : ℝ)+(13154906034076969/100000000000000000000 : ℝ) ≤ ((7432566251325681591/7435000000000000000 : ℝ)+(258593573179/148700000000000 : ℝ)*((7117/50000 : ℝ)+(563/5000 : ℝ)))^(2095/512 : ℝ) := by
    rw [show (7432566251325681591/7435000000000000000 : ℝ)+(258593573179/148700000000000 : ℝ)*((7117/50000 : ℝ)+(563/5000 : ℝ))=(39067031689239/39062500000000 : ℝ) by norm_num, show 1+(17161526339674281/50000000000000000000 : ℝ)+(13154906034076969/100000000000000000000 : ℝ)=(100047477958713425531/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17161526339674281/50000000000000000000 : ℝ) ≤ ((7432566251325681591/7435000000000000000 : ℝ)+2*(258593573179/148700000000000 : ℝ)*(7117/50000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (7432566251325681591/7435000000000000000 : ℝ)+2*(258593573179/148700000000000 : ℝ)*(7117/50000 : ℝ)=(5000838649795771/5000000000000000 : ℝ) by norm_num, show 1+2*(17161526339674281/50000000000000000000 : ℝ)=(25017161526339674281/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7432566251325681591/7435000000000000000 : ℝ)*(X 1 0+X 2 0)+(258593573179/148700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7432566251325681591/7435000000000000000 : ℝ)) (alpha := (258593573179/148700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7432566251325681591/7435000000000000000 : ℝ)*(X 0 1+X 2 1)+(258593573179/148700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7432566251325681591/7435000000000000000 : ℝ)) (alpha := (258593573179/148700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7432566251325681591/7435000000000000000 : ℝ)*(X 0 2+X 1 2)+(258593573179/148700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7432566251325681591/7435000000000000000 : ℝ)) (alpha := (258593573179/148700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2144948597/10000000000 : ℝ)*X 0 0+(5393731293/10000000000 : ℝ)*X 0 1+(5265004239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336239567/2500000000 : ℝ)*X 1 0+(-1105125671/5000000000 : ℝ)*X 1 1+(5265004263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068991663/2000000000 : ℝ)*X 2 0+(2632502129/5000000000 : ℝ)*X 2 1+(-1105125643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358156357/10000000000 : ℝ)*X 0 0+(4230835839/10000000000 : ℝ)*X 0 1+(4489247683/10000000000 : ℝ)*X 0 2+(4358156357/10000000000 : ℝ)*X 1 0+(4230835839/10000000000 : ℝ)*X 1 1+(4489247683/10000000000 : ℝ)*X 1 2+(4358156357/10000000000 : ℝ)*X 2 0+(4230835839/10000000000 : ℝ)*X 2 1+(4489247683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-536238427/2500000000 : ℝ)*X 0 0+(1053067169/2000000000 : ℝ)*X 0 1+(1348349617/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328059021/2500000000 : ℝ)*X 1 0+(-1040928559/5000000000 : ℝ)*X 1 1+(337087401/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212489443/400000000 : ℝ)*X 2 0+(5393398433/10000000000 : ℝ)*X 2 1+(-520464277/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089541651/2500000000 : ℝ)*X 0 0+(4488582041/10000000000 : ℝ)*X 0 1+(4231503987/10000000000 : ℝ)*X 0 2+(1089541651/2500000000 : ℝ)*X 1 0+(4488582041/10000000000 : ℝ)*X 1 1+(4231503987/10000000000 : ℝ)*X 1 2+(1089541651/2500000000 : ℝ)*X 2 0+(4488582041/10000000000 : ℝ)*X 2 1+(4231503987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1149506074963888291351355307/185875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61597719/5000000000000 : ℝ)*(base19) + (1231564617/100000000000000 : ℝ)*(base23) + (1836001/5000000000000 : ℝ)*(lower2) + (28280063/25000000000000 : ℝ)*(upper3) + (163819883/100000000000000 : ℝ)*(upper5) + (2909568451733041/50000000000000 : ℝ)*(major0) + (2909568451733041/50000000000000 : ℝ)*(major1) + (2909568451733041/50000000000000 : ℝ)*(major2) + (7768408404881011/100000000000000 : ℝ)*(sp0) + (194211131184281/2500000000000 : ℝ)*(sp1) + (3884222623880501/50000000000000 : ℝ)*(sp2) + (1934904744270141/50000000000000 : ℝ)*(sp3) + (38074444609/100000000000000 : ℝ)*(sp4) + (110205769/625000000000 : ℝ)*(sp7) + (1934913560731661/50000000000000 : ℝ)*(f.failure) + (388422323966281/5000000000000 : ℝ)*(f.sum) + (14459719213353/7435000000000000000000000000 : ℝ)*base65 + (586469053831598231/371750000000000000000000000000000 : ℝ)*base67 + (5558451999645151769/371750000000000000000000000000000 : ℝ)*base70 + (2161679099132401769/371750000000000000000000000000000 : ℝ)*base72 + (807826848737/1858750000000000000000000000 : ℝ)*base73 + (4550719923036598231/371750000000000000000000000000000 : ℝ)*base75 + (2199238622375098231/371750000000000000000000000000000 : ℝ)*base77 + (8285612414817598231/371750000000000000000000000000000 : ℝ)*base79 + (530386771057/464687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (10832017/1250000000000000000000 : ℝ)*base90 + (10832017/1250000000000000000000 : ℝ)*base92 + (10832017/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66799210573507034088921/7435000000000000000000000000 : ℝ) := by norm_num
    linear_combination (882721271/50000000000000 : ℝ)*(base19) + (467169759/25000000000000 : ℝ)*(base23) + (89926441/50000000000000 : ℝ)*(upper3) + (51635839/100000000000000 : ℝ)*(lower4) + (184530789/100000000000000 : ℝ)*(upper5) + (2924636823478119/50000000000000 : ℝ)*(major0) + (2924636823478119/50000000000000 : ℝ)*(major1) + (2924636823478119/50000000000000 : ℝ)*(major2) + (11542796459/25000000000000 : ℝ)*(sp1) + (12324632871/25000000000000 : ℝ)*(sp2) + (7808678415060423/100000000000000 : ℝ)*(sp4) + (1561726095686409/20000000000000 : ℝ)*(sp5) + (7808627247849903/100000000000000 : ℝ)*(sp6) + (777973715874233/20000000000000 : ℝ)*(sp7) + (777973715874233/20000000000000 : ℝ)*(f.failure) + (7808678415060423/100000000000000 : ℝ)*(f.sum) + (8039215696479/3717500000000000000000000000 : ℝ)*base66 + (2418275144385342671/371750000000000000000000000000000 : ℝ)*base68 + (1774634882501407329/371750000000000000000000000000000 : ℝ)*base69 + (1228232766300657329/371750000000000000000000000000000 : ℝ)*base71 + (37741302911603/7435000000000000000000000000 : ℝ)*base74 + (3592032736720592671/371750000000000000000000000000000 : ℝ)*base76 + (3572300024414092671/371750000000000000000000000000000 : ℝ)*base78 + (3974449962031657329/371750000000000000000000000000000 : ℝ)*base79 + (23442231322057/7435000000000000000000000000 : ℝ)*base81 + (1208301/500000000000000000000 : ℝ)*base90 + (1208301/500000000000000000000 : ℝ)*base92 + (1208301/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1188_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1188_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1188_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1188_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1188_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1188_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1188_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
