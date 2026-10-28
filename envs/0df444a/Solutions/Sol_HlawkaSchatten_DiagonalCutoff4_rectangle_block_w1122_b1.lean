-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1122_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:09:42.417488+00:00
-- url     : https://prove2.me/submissions/2e88f6a7-ff36-4532-82d6-95e5ac485320

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
theorem support_rectangle_w1122_s3_0 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-434491413/2000000000 : ℝ)*x 0 + (5431277371/10000000000 : ℝ)*x 1 + (653770547/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434491413/2000000000 : ℝ)^8315 ≤ (1319084865281/10000000000000 : ℝ)^6267 := by
    have hnat : (434491413 : ℕ)^8315*10000000000000^6267 ≤ 1319084865281^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434491413 2000000000 1319084865281 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431277371/10000000000 : ℝ)^8315 ≤ (44490808936271/100000000000000 : ℝ)^6267 := by
    have hnat : (5431277371 : ℕ)^8315*100000000000000^6267 ≤ 44490808936271^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431277371 10000000000 44490808936271 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653770547/1250000000 : ℝ)^8315 ≤ (21159171199619/50000000000000 : ℝ)^6267 := by
    have hnat : (653770547 : ℕ)^8315*50000000000000^6267 ≤ 21159171199619^6267*1250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653770547 1250000000 21159171199619 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434491413/2000000000 : ℝ), (5431277371/10000000000 : ℝ), (653770547/1250000000 : ℝ)] ![(1319084865281/10000000000000 : ℝ), (44490808936271/100000000000000 : ℝ), (21159171199619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434491413/2000000000 : ℝ)|^8315 ≤ (1319084865281/10000000000000 : ℝ)^6267
        have hw : |(-434491413/2000000000 : ℝ)|=(434491413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431277371/10000000000 : ℝ)|^8315 ≤ (44490808936271/100000000000000 : ℝ)^6267
        have hw : |(5431277371/10000000000 : ℝ)|=(5431277371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653770547/1250000000 : ℝ)|^8315 ≤ (21159171199619/50000000000000 : ℝ)^6267
        have hw : |(653770547/1250000000 : ℝ)|=(653770547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s3_1 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42834247/80000000 : ℝ)*x 0 + (-91012203/400000000 : ℝ)*x 1 + (1307541079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42834247/80000000 : ℝ)^8315 ≤ (8731182942439/20000000000000 : ℝ)^6267 := by
    have hnat : (42834247 : ℕ)^8315*20000000000000^6267 ≤ 8731182942439^6267*80000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42834247 80000000 8731182942439 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91012203/400000000 : ℝ)^8315 ≤ (14025743509643/100000000000000 : ℝ)^6267 := by
    have hnat : (91012203 : ℕ)^8315*100000000000000^6267 ≤ 14025743509643^6267*400000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91012203 400000000 14025743509643 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307541079/2500000000 : ℝ)^8315 ≤ (42318341755117/100000000000000 : ℝ)^6267 := by
    have hnat : (1307541079 : ℕ)^8315*100000000000000^6267 ≤ 42318341755117^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307541079 2500000000 42318341755117 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42834247/80000000 : ℝ), (-91012203/400000000 : ℝ), (1307541079/2500000000 : ℝ)] ![(8731182942439/20000000000000 : ℝ), (14025743509643/100000000000000 : ℝ), (42318341755117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42834247/80000000 : ℝ)|^8315 ≤ (8731182942439/20000000000000 : ℝ)^6267
        have hw : |(42834247/80000000 : ℝ)|=(42834247/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91012203/400000000 : ℝ)|^8315 ≤ (14025743509643/100000000000000 : ℝ)^6267
        have hw : |(-91012203/400000000 : ℝ)|=(91012203/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307541079/2500000000 : ℝ)|^8315 ≤ (42318341755117/100000000000000 : ℝ)^6267
        have hw : |(1307541079/2500000000 : ℝ)|=(1307541079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s3_2 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5354280979/10000000000 : ℝ)*x 0 + (5230164419/10000000000 : ℝ)*x 1 + (-568826201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354280979/10000000000 : ℝ)^8315 ≤ (43655915837261/100000000000000 : ℝ)^6267 := by
    have hnat : (5354280979 : ℕ)^8315*100000000000000^6267 ≤ 43655915837261^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354280979 10000000000 43655915837261 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230164419/10000000000 : ℝ)^8315 ≤ (42318342860857/100000000000000 : ℝ)^6267 := by
    have hnat : (5230164419 : ℕ)^8315*100000000000000^6267 ≤ 42318342860857^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230164419 10000000000 42318342860857 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568826201/2500000000 : ℝ)^8315 ≤ (1753217661649/12500000000000 : ℝ)^6267 := by
    have hnat : (568826201 : ℕ)^8315*12500000000000^6267 ≤ 1753217661649^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568826201 2500000000 1753217661649 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354280979/10000000000 : ℝ), (5230164419/10000000000 : ℝ), (-568826201/2500000000 : ℝ)] ![(43655915837261/100000000000000 : ℝ), (42318342860857/100000000000000 : ℝ), (1753217661649/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354280979/10000000000 : ℝ)|^8315 ≤ (43655915837261/100000000000000 : ℝ)^6267
        have hw : |(5354280979/10000000000 : ℝ)|=(5354280979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230164419/10000000000 : ℝ)|^8315 ≤ (42318342860857/100000000000000 : ℝ)^6267
        have hw : |(5230164419/10000000000 : ℝ)|=(5230164419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-568826201/2500000000 : ℝ)|^8315 ≤ (1753217661649/12500000000000 : ℝ)^6267
        have hw : |(-568826201/2500000000 : ℝ)|=(568826201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s3_3 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365108803/10000000000 : ℝ)*x 0 + (4170379791/10000000000 : ℝ)*x 1 + (4568919341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365108803/10000000000 : ℝ)^8315 ≤ (33292672380267/100000000000000 : ℝ)^6267 := by
    have hnat : (4365108803 : ℕ)^8315*100000000000000^6267 ≤ 33292672380267^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365108803 10000000000 33292672380267 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170379791/10000000000 : ℝ)^8315 ≤ (31336635473167/100000000000000 : ℝ)^6267 := by
    have hnat : (4170379791 : ℕ)^8315*100000000000000^6267 ≤ 31336635473167^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170379791 10000000000 31336635473167 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4568919341/10000000000 : ℝ)^8315 ≤ (35370692132283/100000000000000 : ℝ)^6267 := by
    have hnat : (4568919341 : ℕ)^8315*100000000000000^6267 ≤ 35370692132283^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4568919341 10000000000 35370692132283 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365108803/10000000000 : ℝ), (4170379791/10000000000 : ℝ), (4568919341/10000000000 : ℝ)] ![(33292672380267/100000000000000 : ℝ), (31336635473167/100000000000000 : ℝ), (35370692132283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365108803/10000000000 : ℝ)|^8315 ≤ (33292672380267/100000000000000 : ℝ)^6267
        have hw : |(4365108803/10000000000 : ℝ)|=(4365108803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170379791/10000000000 : ℝ)|^8315 ≤ (31336635473167/100000000000000 : ℝ)^6267
        have hw : |(4170379791/10000000000 : ℝ)|=(4170379791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4568919341/10000000000 : ℝ)|^8315 ≤ (35370692132283/100000000000000 : ℝ)^6267
        have hw : |(4568919341/10000000000 : ℝ)|=(4568919341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s3_4 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-543119027/2500000000 : ℝ)*x 0 + (40866843/78125000 : ℝ)*x 1 + (5430481389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543119027/2500000000 : ℝ)^8315 ≤ (3297750516269/25000000000000 : ℝ)^6267 := by
    have hnat : (543119027 : ℕ)^8315*25000000000000^6267 ≤ 3297750516269^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543119027 2500000000 3297750516269 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40866843/78125000 : ℝ)^8315 ≤ (42326839932827/100000000000000 : ℝ)^6267 := by
    have hnat : (40866843 : ℕ)^8315*100000000000000^6267 ≤ 42326839932827^6267*78125000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40866843 78125000 42326839932827 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430481389/10000000000 : ℝ)^8315 ≤ (44482157987799/100000000000000 : ℝ)^6267 := by
    have hnat : (5430481389 : ℕ)^8315*100000000000000^6267 ≤ 44482157987799^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430481389 10000000000 44482157987799 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543119027/2500000000 : ℝ), (40866843/78125000 : ℝ), (5430481389/10000000000 : ℝ)] ![(3297750516269/25000000000000 : ℝ), (42326839932827/100000000000000 : ℝ), (44482157987799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543119027/2500000000 : ℝ)|^8315 ≤ (3297750516269/25000000000000 : ℝ)^6267
        have hw : |(-543119027/2500000000 : ℝ)|=(543119027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40866843/78125000 : ℝ)|^8315 ≤ (42326839932827/100000000000000 : ℝ)^6267
        have hw : |(40866843/78125000 : ℝ)|=(40866843/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430481389/10000000000 : ℝ)|^8315 ≤ (44482157987799/100000000000000 : ℝ)^6267
        have hw : |(5430481389/10000000000 : ℝ)|=(5430481389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s3_5 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2651702393/5000000000 : ℝ)*x 0 + (-16210843/78125000 : ℝ)*x 1 + (5430481501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651702393/5000000000 : ℝ)^8315 ≤ (21553198322997/50000000000000 : ℝ)^6267 := by
    have hnat : (2651702393 : ℕ)^8315*50000000000000^6267 ≤ 21553198322997^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651702393 5000000000 21553198322997 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16210843/78125000 : ℝ)^8315 ≤ (155143051673/1250000000000 : ℝ)^6267 := by
    have hnat : (16210843 : ℕ)^8315*1250000000000^6267 ≤ 155143051673^6267*78125000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16210843 78125000 155143051673 1250000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430481501/10000000000 : ℝ)^8315 ≤ (5560269900627/12500000000000 : ℝ)^6267 := by
    have hnat : (5430481501 : ℕ)^8315*12500000000000^6267 ≤ 5560269900627^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430481501 10000000000 5560269900627 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651702393/5000000000 : ℝ), (-16210843/78125000 : ℝ), (5430481501/10000000000 : ℝ)] ![(21553198322997/50000000000000 : ℝ), (155143051673/1250000000000 : ℝ), (5560269900627/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651702393/5000000000 : ℝ)|^8315 ≤ (21553198322997/50000000000000 : ℝ)^6267
        have hw : |(2651702393/5000000000 : ℝ)|=(2651702393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16210843/78125000 : ℝ)|^8315 ≤ (155143051673/1250000000000 : ℝ)^6267
        have hw : |(-16210843/78125000 : ℝ)|=(16210843/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430481501/10000000000 : ℝ)|^8315 ≤ (5560269900627/12500000000000 : ℝ)^6267
        have hw : |(5430481501/10000000000 : ℝ)|=(5430481501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s3_6 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303404773/10000000000 : ℝ)*x 0 + (1086096283/2000000000 : ℝ)*x 1 + (-1037494019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303404773/10000000000 : ℝ)^8315 ≤ (43106396505799/100000000000000 : ℝ)^6267 := by
    have hnat : (5303404773 : ℕ)^8315*100000000000000^6267 ≤ 43106396505799^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303404773 10000000000 43106396505799 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086096283/2000000000 : ℝ)^8315 ≤ (44482158270367/100000000000000 : ℝ)^6267 := by
    have hnat : (1086096283 : ℕ)^8315*100000000000000^6267 ≤ 44482158270367^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086096283 2000000000 44482158270367 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037494019/5000000000 : ℝ)^8315 ≤ (12411445197283/100000000000000 : ℝ)^6267 := by
    have hnat : (1037494019 : ℕ)^8315*100000000000000^6267 ≤ 12411445197283^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037494019 5000000000 12411445197283 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303404773/10000000000 : ℝ), (1086096283/2000000000 : ℝ), (-1037494019/5000000000 : ℝ)] ![(43106396505799/100000000000000 : ℝ), (44482158270367/100000000000000 : ℝ), (12411445197283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303404773/10000000000 : ℝ)|^8315 ≤ (43106396505799/100000000000000 : ℝ)^6267
        have hw : |(5303404773/10000000000 : ℝ)|=(5303404773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086096283/2000000000 : ℝ)|^8315 ≤ (44482158270367/100000000000000 : ℝ)^6267
        have hw : |(1086096283/2000000000 : ℝ)|=(1086096283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1037494019/5000000000 : ℝ)|^8315 ≤ (12411445197283/100000000000000 : ℝ)^6267
        have hw : |(-1037494019/5000000000 : ℝ)|=(1037494019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s3_7 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873029303/2000000000 : ℝ)*x 0 + (456735129/1000000000 : ℝ)*x 1 + (260747303/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873029303/2000000000 : ℝ)^8315 ≤ (33293054004831/100000000000000 : ℝ)^6267 := by
    have hnat : (873029303 : ℕ)^8315*100000000000000^6267 ≤ 33293054004831^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873029303 2000000000 33293054004831 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456735129/1000000000 : ℝ)^8315 ≤ (7070917369171/20000000000000 : ℝ)^6267 := by
    have hnat : (456735129 : ℕ)^8315*20000000000000^6267 ≤ 7070917369171^6267*1000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456735129 1000000000 7070917369171 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260747303/625000000 : ℝ)^8315 ≤ (31352359129359/100000000000000 : ℝ)^6267 := by
    have hnat : (260747303 : ℕ)^8315*100000000000000^6267 ≤ 31352359129359^6267*625000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260747303 625000000 31352359129359 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873029303/2000000000 : ℝ), (456735129/1000000000 : ℝ), (260747303/625000000 : ℝ)] ![(33293054004831/100000000000000 : ℝ), (7070917369171/20000000000000 : ℝ), (31352359129359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873029303/2000000000 : ℝ)|^8315 ≤ (33293054004831/100000000000000 : ℝ)^6267
        have hw : |(873029303/2000000000 : ℝ)|=(873029303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(456735129/1000000000 : ℝ)|^8315 ≤ (7070917369171/20000000000000 : ℝ)^6267
        have hw : |(456735129/1000000000 : ℝ)|=(456735129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260747303/625000000 : ℝ)|^8315 ≤ (31352359129359/100000000000000 : ℝ)^6267
        have hw : |(260747303/625000000 : ℝ)|=(260747303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1122_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16563/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (423/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1483/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16563/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16563/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16563/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16563/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16563/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16563/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8979/100000 : ℝ) ^ (4157/1024 : ℝ) ≤ (563060873059399/10000000000000000000 : ℝ) := by
    have hpowers : (8979/100000 : ℝ)^4157 ≤ (563060873059399/10000000000000000000 : ℝ)^1024 := by
      have hnat : (8979 : ℕ)^4157*10000000000000000000^1024 ≤ 563060873059399^1024*100000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8979 100000 563060873059399 10000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8979/100000 : ℝ)) (X := (563060873059399/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16563/100000 : ℝ) ^ (4157/1024 : ℝ) ≤ (13522901025272289/20000000000000000000 : ℝ) := by
    have hpowers : (16563/100000 : ℝ)^4157 ≤ (13522901025272289/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16563 : ℕ)^4157*20000000000000000000^1024 ≤ 13522901025272289^1024*100000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16563 100000 13522901025272289 20000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16563/100000 : ℝ)) (X := (13522901025272289/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000563060873059399/5000000000000000000 : ℝ) ≤ (2500069346868901/2500000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (5000563060873059399/5000000000000000000 : ℝ)^1024 ≤ (2500069346868901/2500000000000000 : ℝ)^4157 := by
      have hnat : (5000563060873059399 : ℕ)^1024*2500000000000000^4157 ≤ 2500069346868901^4157*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000563060873059399 5000000000000000000 2500069346868901 2500000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500069346868901/2500000000000000 : ℝ)) (X := (5000563060873059399/5000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20014649022771391087/20000000000000000000 : ℝ) ≤ (5000901880005661/5000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (20014649022771391087/20000000000000000000 : ℝ)^1024 ≤ (5000901880005661/5000000000000000 : ℝ)^4157 := by
      have hnat : (20014649022771391087 : ℕ)^1024*5000000000000000^4157 ≤ 5000901880005661^4157*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20014649022771391087 20000000000000000000 5000901880005661 5000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000901880005661/5000000000000000 : ℝ)) (X := (20014649022771391087/20000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10013522901025272289/10000000000000000000 : ℝ) ≤ (62520813328419/62500000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (10013522901025272289/10000000000000000000 : ℝ)^1024 ≤ (62520813328419/62500000000000 : ℝ)^4157 := by
      have hnat : (10013522901025272289 : ℕ)^1024*62500000000000^4157 ≤ 62520813328419^4157*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10013522901025272289 10000000000000000000 62520813328419 62500000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62520813328419/62500000000000 : ℝ)) (X := (10013522901025272289/10000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(563060873059399/10000000000000000000 : ℝ) ≤ ((6317891092384879741/6320000000000000000 : ℝ)+2*(763186267859/379200000000000 : ℝ)*(8979/100000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (6317891092384879741/6320000000000000000 : ℝ)+2*(763186267859/379200000000000 : ℝ)*(8979/100000 : ℝ)=(2500069346868901/2500000000000000 : ℝ) by norm_num, show 1+2*(563060873059399/10000000000000000000 : ℝ)=(5000563060873059399/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13522901025272289/20000000000000000000 : ℝ)+(563060873059399/10000000000000000000 : ℝ) ≤ ((6317891092384879741/6320000000000000000 : ℝ)+(763186267859/379200000000000 : ℝ)*((16563/100000 : ℝ)+(8979/100000 : ℝ)))^(4157/1024 : ℝ) := by
    rw [show (6317891092384879741/6320000000000000000 : ℝ)+(763186267859/379200000000000 : ℝ)*((16563/100000 : ℝ)+(8979/100000 : ℝ))=(5000901880005661/5000000000000000 : ℝ) by norm_num, show 1+(13522901025272289/20000000000000000000 : ℝ)+(563060873059399/10000000000000000000 : ℝ)=(20014649022771391087/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13522901025272289/20000000000000000000 : ℝ) ≤ ((6317891092384879741/6320000000000000000 : ℝ)+2*(763186267859/379200000000000 : ℝ)*(16563/100000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (6317891092384879741/6320000000000000000 : ℝ)+2*(763186267859/379200000000000 : ℝ)*(16563/100000 : ℝ)=(62520813328419/62500000000000 : ℝ) by norm_num, show 1+2*(13522901025272289/20000000000000000000 : ℝ)=(10013522901025272289/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6317891092384879741/6320000000000000000 : ℝ)*(X 1 0+X 2 0)+(763186267859/379200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (8979/100000 : ℝ)) (hi := (16563/100000 : ℝ)) (c := (6317891092384879741/6320000000000000000 : ℝ)) (alpha := (763186267859/379200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6317891092384879741/6320000000000000000 : ℝ)*(X 0 1+X 2 1)+(763186267859/379200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (8979/100000 : ℝ)) (hi := (16563/100000 : ℝ)) (c := (6317891092384879741/6320000000000000000 : ℝ)) (alpha := (763186267859/379200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6317891092384879741/6320000000000000000 : ℝ)*(X 0 2+X 1 2)+(763186267859/379200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (8979/100000 : ℝ)) (hi := (16563/100000 : ℝ)) (c := (6317891092384879741/6320000000000000000 : ℝ)) (alpha := (763186267859/379200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-434491413/2000000000 : ℝ)*X 0 0+(5431277371/10000000000 : ℝ)*X 0 1+(653770547/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42834247/80000000 : ℝ)*X 1 0+(-91012203/400000000 : ℝ)*X 1 1+(1307541079/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354280979/10000000000 : ℝ)*X 2 0+(5230164419/10000000000 : ℝ)*X 2 1+(-568826201/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365108803/10000000000 : ℝ)*X 0 0+(4170379791/10000000000 : ℝ)*X 0 1+(4568919341/10000000000 : ℝ)*X 0 2+(4365108803/10000000000 : ℝ)*X 1 0+(4170379791/10000000000 : ℝ)*X 1 1+(4568919341/10000000000 : ℝ)*X 1 2+(4365108803/10000000000 : ℝ)*X 2 0+(4170379791/10000000000 : ℝ)*X 2 1+(4568919341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-543119027/2500000000 : ℝ)*X 0 0+(40866843/78125000 : ℝ)*X 0 1+(5430481389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651702393/5000000000 : ℝ)*X 1 0+(-16210843/78125000 : ℝ)*X 1 1+(5430481501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303404773/10000000000 : ℝ)*X 2 0+(1086096283/2000000000 : ℝ)*X 2 1+(-1037494019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873029303/2000000000 : ℝ)*X 0 0+(456735129/1000000000 : ℝ)*X 0 1+(260747303/625000000 : ℝ)*X 0 2+(873029303/2000000000 : ℝ)*X 1 0+(456735129/1000000000 : ℝ)*X 1 1+(260747303/625000000 : ℝ)*X 1 2+(873029303/2000000000 : ℝ)*X 2 0+(456735129/1000000000 : ℝ)*X 2 1+(260747303/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (349213173786212017844050329/158000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (871357189/100000000000000 : ℝ)*(base19) + (168772321/20000000000000 : ℝ)*(base23) + (18545459/25000000000000 : ℝ)*(lower2) + (67265143/50000000000000 : ℝ)*(upper5) + (1870384916666577/50000000000000 : ℝ)*(major0) + (1870384916666577/50000000000000 : ℝ)*(major1) + (1870384916666577/50000000000000 : ℝ)*(major2) + (1243085854721363/25000000000000 : ℝ)*(sp0) + (497236180644673/10000000000000 : ℝ)*(sp1) + (4972363356730207/100000000000000 : ℝ)*(sp2) + (1254584379574121/50000000000000 : ℝ)*(sp3) + (519542659/2500000000000 : ℝ)*(sp4) + (761393947/50000000000000 : ℝ)*(sp5) + (6633252581/100000000000000 : ℝ)*(sp7) + (313646924050103/12500000000000 : ℝ)*(f.failure) + (1243091050147953/25000000000000 : ℝ)*(f.sum) + (8481631754921/3160000000000000000000000000 : ℝ)*base65 + (691150544979166557/316000000000000000000000000000000 : ℝ)*base67 + (568810463051166557/316000000000000000000000000000000 : ℝ)*base69 + (171262310783166557/316000000000000000000000000000000 : ℝ)*base71 + (24806022047121/3160000000000000000000000000 : ℝ)*base73 + (1958128908860833443/316000000000000000000000000000000 : ℝ)*base76 + (1521504013579166557/316000000000000000000000000000000 : ℝ)*base77 + (3830445612936833443/316000000000000000000000000000000 : ℝ)*base80 + (15278019131761/3160000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4264199/1250000000000000000000 : ℝ)*base89 + (4264199/1250000000000000000000 : ℝ)*base91 + (4264199/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (391732050936654316820254321/79000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (951311337/100000000000000 : ℝ)*(base19) + (556260193/50000000000000 : ℝ)*(base23) + (61213967/50000000000000 : ℝ)*(upper3) + (88241133/100000000000000 : ℝ)*(lower4) + (73583881/100000000000000 : ℝ)*(upper5) + (1885252011676127/50000000000000 : ℝ)*(major0) + (1885252011676127/50000000000000 : ℝ)*(major1) + (1885252011676127/50000000000000 : ℝ)*(major2) + (18391267053/100000000000000 : ℝ)*(sp1) + (19132240099/100000000000000 : ℝ)*(sp2) + (250594392580979/5000000000000 : ℝ)*(sp4) + (501186850904119/10000000000000 : ℝ)*(sp5) + (1002373521371819/20000000000000 : ℝ)*(sp6) + (2529120029797137/100000000000000 : ℝ)*(sp7) + (2529120029797137/100000000000000 : ℝ)*(f.failure) + (250594392580979/5000000000000 : ℝ)*(f.sum) + (37561165667893/9480000000000000000000000000 : ℝ)*base65 + (12310554236088420679/948000000000000000000000000000000 : ℝ)*base68 + (3477359227296420679/948000000000000000000000000000000 : ℝ)*base70 + (1007786639351579321/948000000000000000000000000000000 : ℝ)*base71 + (7741517810507/9480000000000000000000000000 : ℝ)*base74 + (10559971808760420679/948000000000000000000000000000000 : ℝ)*base76 + (7984553288316420679/948000000000000000000000000000000 : ℝ)*base78 + (8056931879616420679/948000000000000000000000000000000 : ℝ)*base80 + (35022705546493/9480000000000000000000000000 : ℝ)*base81 + (36958721/10000000000000000000000 : ℝ)*base89 + (36958721/10000000000000000000000 : ℝ)*base91 + (36958721/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1122_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16563/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (423/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1483/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1122_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1122_s4_0 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-27195319/125000000 : ℝ)*x 0 + (675358407/1250000000 : ℝ)*x 1 + (328531403/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27195319/125000000 : ℝ)^8315 ≤ (41301187749/312500000000 : ℝ)^6267 := by
    have hnat : (27195319 : ℕ)^8315*312500000000^6267 ≤ 41301187749^6267*125000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27195319 125000000 41301187749 312500000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675358407/1250000000 : ℝ)^8315 ≤ (44182296919247/100000000000000 : ℝ)^6267 := by
    have hnat : (675358407 : ℕ)^8315*100000000000000^6267 ≤ 44182296919247^6267*1250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675358407 1250000000 44182296919247 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328531403/625000000 : ℝ)^8315 ≤ (213006614951/500000000000 : ℝ)^6267 := by
    have hnat : (328531403 : ℕ)^8315*500000000000^6267 ≤ 213006614951^6267*625000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328531403 625000000 213006614951 500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27195319/125000000 : ℝ), (675358407/1250000000 : ℝ), (328531403/625000000 : ℝ)] ![(41301187749/312500000000 : ℝ), (44182296919247/100000000000000 : ℝ), (213006614951/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27195319/125000000 : ℝ)|^8315 ≤ (41301187749/312500000000 : ℝ)^6267
        have hw : |(-27195319/125000000 : ℝ)|=(27195319/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675358407/1250000000 : ℝ)|^8315 ≤ (44182296919247/100000000000000 : ℝ)^6267
        have hw : |(675358407/1250000000 : ℝ)|=(675358407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328531403/625000000 : ℝ)|^8315 ≤ (213006614951/500000000000 : ℝ)^6267
        have hw : |(328531403/625000000 : ℝ)|=(328531403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s4_1 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347201001/10000000000 : ℝ)*x 0 + (-2250021929/10000000000 : ℝ)*x 1 + (5256502531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347201001/10000000000 : ℝ)^8315 ≤ (10894835406087/25000000000000 : ℝ)^6267 := by
    have hnat : (5347201001 : ℕ)^8315*25000000000000^6267 ≤ 10894835406087^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347201001 10000000000 10894835406087 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250021929/10000000000 : ℝ)^8315 ≤ (6909667236537/50000000000000 : ℝ)^6267 := by
    have hnat : (2250021929 : ℕ)^8315*50000000000000^6267 ≤ 6909667236537^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250021929 10000000000 6909667236537 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256502531/10000000000 : ℝ)^8315 ≤ (42601323882697/100000000000000 : ℝ)^6267 := by
    have hnat : (5256502531 : ℕ)^8315*100000000000000^6267 ≤ 42601323882697^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256502531 10000000000 42601323882697 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347201001/10000000000 : ℝ), (-2250021929/10000000000 : ℝ), (5256502531/10000000000 : ℝ)] ![(10894835406087/25000000000000 : ℝ), (6909667236537/50000000000000 : ℝ), (42601323882697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347201001/10000000000 : ℝ)|^8315 ≤ (10894835406087/25000000000000 : ℝ)^6267
        have hw : |(5347201001/10000000000 : ℝ)|=(5347201001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2250021929/10000000000 : ℝ)|^8315 ≤ (6909667236537/50000000000000 : ℝ)^6267
        have hw : |(-2250021929/10000000000 : ℝ)|=(2250021929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256502531/10000000000 : ℝ)|^8315 ≤ (42601323882697/100000000000000 : ℝ)^6267
        have hw : |(5256502531/10000000000 : ℝ)|=(5256502531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s4_2 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347200789/10000000000 : ℝ)*x 0 + (5256502343/10000000000 : ℝ)*x 1 + (-2250022459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347200789/10000000000 : ℝ)^8315 ≤ (1361854354123/3125000000000 : ℝ)^6267 := by
    have hnat : (5347200789 : ℕ)^8315*3125000000000^6267 ≤ 1361854354123^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347200789 10000000000 1361854354123 3125000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256502343/10000000000 : ℝ)^8315 ≤ (42601321861137/100000000000000 : ℝ)^6267 := by
    have hnat : (5256502343 : ℕ)^8315*100000000000000^6267 ≤ 42601321861137^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256502343 10000000000 42601321861137 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250022459/10000000000 : ℝ)^8315 ≤ (1381933879203/10000000000000 : ℝ)^6267 := by
    have hnat : (2250022459 : ℕ)^8315*10000000000000^6267 ≤ 1381933879203^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250022459 10000000000 1381933879203 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347200789/10000000000 : ℝ), (5256502343/10000000000 : ℝ), (-2250022459/10000000000 : ℝ)] ![(1361854354123/3125000000000 : ℝ), (42601321861137/100000000000000 : ℝ), (1381933879203/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347200789/10000000000 : ℝ)|^8315 ≤ (1361854354123/3125000000000 : ℝ)^6267
        have hw : |(5347200789/10000000000 : ℝ)|=(5347200789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256502343/10000000000 : ℝ)|^8315 ≤ (42601321861137/100000000000000 : ℝ)^6267
        have hw : |(5256502343/10000000000 : ℝ)|=(5256502343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2250022459/10000000000 : ℝ)|^8315 ≤ (1381933879203/10000000000000 : ℝ)^6267
        have hw : |(-2250022459/10000000000 : ℝ)|=(2250022459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s4_3 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1091749337/2500000000 : ℝ)*x 0 + (4224380131/10000000000 : ℝ)*x 1 + (1128607017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091749337/2500000000 : ℝ)^8315 ≤ (16655892367061/50000000000000 : ℝ)^6267 := by
    have hnat : (1091749337 : ℕ)^8315*50000000000000^6267 ≤ 16655892367061^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091749337 2500000000 16655892367061 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224380131/10000000000 : ℝ)^8315 ≤ (7969033742059/25000000000000 : ℝ)^6267 := by
    have hnat : (4224380131 : ℕ)^8315*25000000000000^6267 ≤ 7969033742059^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224380131 10000000000 7969033742059 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128607017/2500000000 : ℝ)^8315 ≤ (17406040139789/50000000000000 : ℝ)^6267 := by
    have hnat : (1128607017 : ℕ)^8315*50000000000000^6267 ≤ 17406040139789^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128607017 2500000000 17406040139789 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091749337/2500000000 : ℝ), (4224380131/10000000000 : ℝ), (1128607017/2500000000 : ℝ)] ![(16655892367061/50000000000000 : ℝ), (7969033742059/25000000000000 : ℝ), (17406040139789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091749337/2500000000 : ℝ)|^8315 ≤ (16655892367061/50000000000000 : ℝ)^6267
        have hw : |(1091749337/2500000000 : ℝ)|=(1091749337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224380131/10000000000 : ℝ)|^8315 ≤ (7969033742059/25000000000000 : ℝ)^6267
        have hw : |(4224380131/10000000000 : ℝ)|=(4224380131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1128607017/2500000000 : ℝ)|^8315 ≤ (17406040139789/50000000000000 : ℝ)^6267
        have hw : |(1128607017/2500000000 : ℝ)|=(1128607017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s4_4 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2175632741/10000000000 : ℝ)*x 0 + (1051384471/2000000000 : ℝ)*x 1 + (2701222863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175632741/10000000000 : ℝ)^8315 ≤ (13216438280421/100000000000000 : ℝ)^6267 := by
    have hnat : (2175632741 : ℕ)^8315*100000000000000^6267 ≤ 13216438280421^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175632741 10000000000 13216438280421 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051384471/2000000000 : ℝ)^8315 ≤ (10651459575011/25000000000000 : ℝ)^6267 := by
    have hnat : (1051384471 : ℕ)^8315*25000000000000^6267 ≤ 10651459575011^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051384471 2000000000 10651459575011 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701222863/5000000000 : ℝ)^8315 ≤ (11044430852653/25000000000000 : ℝ)^6267 := by
    have hnat : (2701222863 : ℕ)^8315*25000000000000^6267 ≤ 11044430852653^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701222863 5000000000 11044430852653 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2175632741/10000000000 : ℝ), (1051384471/2000000000 : ℝ), (2701222863/5000000000 : ℝ)] ![(13216438280421/100000000000000 : ℝ), (10651459575011/25000000000000 : ℝ), (11044430852653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2175632741/10000000000 : ℝ)|^8315 ≤ (13216438280421/100000000000000 : ℝ)^6267
        have hw : |(-2175632741/10000000000 : ℝ)|=(2175632741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051384471/2000000000 : ℝ)|^8315 ≤ (10651459575011/25000000000000 : ℝ)^6267
        have hw : |(1051384471/2000000000 : ℝ)|=(1051384471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701222863/5000000000 : ℝ)|^8315 ≤ (11044430852653/25000000000000 : ℝ)^6267
        have hw : |(2701222863/5000000000 : ℝ)|=(2701222863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s4_5 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531017589/1000000000 : ℝ)*x 0 + (-2104079059/10000000000 : ℝ)*x 1 + (1350611447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531017589/1000000000 : ℝ)^8315 ≤ (8635886615729/20000000000000 : ℝ)^6267 := by
    have hnat : (531017589 : ℕ)^8315*20000000000000^6267 ≤ 8635886615729^6267*1000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531017589 1000000000 8635886615729 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104079059/10000000000 : ℝ)^8315 ≤ (12642842829399/100000000000000 : ℝ)^6267 := by
    have hnat : (2104079059 : ℕ)^8315*100000000000000^6267 ≤ 12642842829399^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104079059 10000000000 12642842829399 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350611447/2500000000 : ℝ)^8315 ≤ (4417772408329/10000000000000 : ℝ)^6267 := by
    have hnat : (1350611447 : ℕ)^8315*10000000000000^6267 ≤ 4417772408329^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350611447 2500000000 4417772408329 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531017589/1000000000 : ℝ), (-2104079059/10000000000 : ℝ), (1350611447/2500000000 : ℝ)] ![(8635886615729/20000000000000 : ℝ), (12642842829399/100000000000000 : ℝ), (4417772408329/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531017589/1000000000 : ℝ)|^8315 ≤ (8635886615729/20000000000000 : ℝ)^6267
        have hw : |(531017589/1000000000 : ℝ)|=(531017589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2104079059/10000000000 : ℝ)|^8315 ≤ (12642842829399/100000000000000 : ℝ)^6267
        have hw : |(-2104079059/10000000000 : ℝ)|=(2104079059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350611447/2500000000 : ℝ)|^8315 ≤ (4417772408329/10000000000000 : ℝ)^6267
        have hw : |(1350611447/2500000000 : ℝ)|=(1350611447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s4_6 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265508797/500000000 : ℝ)*x 0 + (2701222907/5000000000 : ℝ)*x 1 + (-526019739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265508797/500000000 : ℝ)^8315 ≤ (21589716809041/50000000000000 : ℝ)^6267 := by
    have hnat : (265508797 : ℕ)^8315*50000000000000^6267 ≤ 21589716809041^6267*500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265508797 500000000 21589716809041 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701222907/5000000000 : ℝ)^8315 ≤ (44177724365381/100000000000000 : ℝ)^6267 := by
    have hnat : (2701222907 : ℕ)^8315*100000000000000^6267 ≤ 44177724365381^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701222907 5000000000 44177724365381 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526019739/2500000000 : ℝ)^8315 ≤ (12642842008249/100000000000000 : ℝ)^6267 := by
    have hnat : (526019739 : ℕ)^8315*100000000000000^6267 ≤ 12642842008249^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526019739 2500000000 12642842008249 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265508797/500000000 : ℝ), (2701222907/5000000000 : ℝ), (-526019739/2500000000 : ℝ)] ![(21589716809041/50000000000000 : ℝ), (44177724365381/100000000000000 : ℝ), (12642842008249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265508797/500000000 : ℝ)|^8315 ≤ (21589716809041/50000000000000 : ℝ)^6267
        have hw : |(265508797/500000000 : ℝ)|=(265508797/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701222907/5000000000 : ℝ)|^8315 ≤ (44177724365381/100000000000000 : ℝ)^6267
        have hw : |(2701222907/5000000000 : ℝ)|=(2701222907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526019739/2500000000 : ℝ)|^8315 ≤ (12642842008249/100000000000000 : ℝ)^6267
        have hw : |(-526019739/2500000000 : ℝ)|=(526019739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s4_7 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873402457/2000000000 : ℝ)*x 0 + (2256797769/5000000000 : ℝ)*x 1 + (1056303943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873402457/2000000000 : ℝ)^8315 ≤ (8327983977383/25000000000000 : ℝ)^6267 := by
    have hnat : (873402457 : ℕ)^8315*25000000000000^6267 ≤ 8327983977383^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873402457 2000000000 8327983977383 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256797769/5000000000 : ℝ)^8315 ≤ (34803562692097/100000000000000 : ℝ)^6267 := by
    have hnat : (2256797769 : ℕ)^8315*100000000000000^6267 ≤ 34803562692097^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256797769 5000000000 34803562692097 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056303943/2500000000 : ℝ)^8315 ≤ (31884501375491/100000000000000 : ℝ)^6267 := by
    have hnat : (1056303943 : ℕ)^8315*100000000000000^6267 ≤ 31884501375491^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056303943 2500000000 31884501375491 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873402457/2000000000 : ℝ), (2256797769/5000000000 : ℝ), (1056303943/2500000000 : ℝ)] ![(8327983977383/25000000000000 : ℝ), (34803562692097/100000000000000 : ℝ), (31884501375491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873402457/2000000000 : ℝ)|^8315 ≤ (8327983977383/25000000000000 : ℝ)^6267
        have hw : |(873402457/2000000000 : ℝ)|=(873402457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256797769/5000000000 : ℝ)|^8315 ≤ (34803562692097/100000000000000 : ℝ)^6267
        have hw : |(2256797769/5000000000 : ℝ)|=(2256797769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056303943/2500000000 : ℝ)|^8315 ≤ (31884501375491/100000000000000 : ℝ)^6267
        have hw : |(1056303943/2500000000 : ℝ)|=(1056303943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1122_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1483/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (423/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (11137/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1483/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (423/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1483/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (423/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1483/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (423/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1483/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (423/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1483/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (423/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1483/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (423/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (423/4000 : ℝ) ^ (4157/1024 : ℝ) ≤ (10939502737010423/100000000000000000000 : ℝ) := by
    have hpowers : (423/4000 : ℝ)^4157 ≤ (10939502737010423/100000000000000000000 : ℝ)^1024 := by
      have hnat : (423 : ℕ)^4157*100000000000000000000^1024 ≤ 10939502737010423^1024*4000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        423 4000 10939502737010423 100000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (423/4000 : ℝ)) (X := (10939502737010423/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1483/10000 : ℝ) ^ (4157/1024 : ℝ) ≤ (2158535660010721/5000000000000000000 : ℝ) := by
    have hpowers : (1483/10000 : ℝ)^4157 ≤ (2158535660010721/5000000000000000000 : ℝ)^1024 := by
      have hnat : (1483 : ℕ)^4157*5000000000000000000^1024 ≤ 2158535660010721^1024*10000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1483 10000 2158535660010721 5000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1483/10000 : ℝ)) (X := (2158535660010721/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010939502737010423/50000000000000000000 : ℝ) ≤ (10000538904370399/10000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (50010939502737010423/50000000000000000000 : ℝ)^1024 ≤ (10000538904370399/10000000000000000 : ℝ)^4157 := by
      have hnat : (50010939502737010423 : ℕ)^1024*10000000000000000^4157 ≤ 10000538904370399^4157*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010939502737010423 50000000000000000000 10000538904370399 10000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538904370399/10000000000000000 : ℝ)) (X := (50010939502737010423/50000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100054110215937224843/100000000000000000000 : ℝ) ≤ (10001332633305323/10000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (100054110215937224843/100000000000000000000 : ℝ)^1024 ≤ (10001332633305323/10000000000000000 : ℝ)^4157 := by
      have hnat : (100054110215937224843 : ℕ)^1024*10000000000000000^4157 ≤ 10001332633305323^4157*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054110215937224843 100000000000000000000 10001332633305323 10000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001332633305323/10000000000000000 : ℝ)) (X := (100054110215937224843/100000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502158535660010721/2500000000000000000 : ℝ) ≤ (10002126362240247/10000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (2502158535660010721/2500000000000000000 : ℝ)^1024 ≤ (10002126362240247/10000000000000000 : ℝ)^4157 := by
      have hnat : (2502158535660010721 : ℕ)^1024*10000000000000000^4157 ≤ 10002126362240247^4157*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502158535660010721 2500000000000000000 10002126362240247 10000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002126362240247/10000000000000000 : ℝ)) (X := (2502158535660010721/2500000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10939502737010423/100000000000000000000 : ℝ) ≤ ((8507101134224481029/8510000000000000000 : ℝ)+2*(198432233731/106375000000000 : ℝ)*(423/4000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (8507101134224481029/8510000000000000000 : ℝ)+2*(198432233731/106375000000000 : ℝ)*(423/4000 : ℝ)=(10000538904370399/10000000000000000 : ℝ) by norm_num, show 1+2*(10939502737010423/100000000000000000000 : ℝ)=(50010939502737010423/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2158535660010721/5000000000000000000 : ℝ)+(10939502737010423/100000000000000000000 : ℝ) ≤ ((8507101134224481029/8510000000000000000 : ℝ)+(198432233731/106375000000000 : ℝ)*((1483/10000 : ℝ)+(423/4000 : ℝ)))^(4157/1024 : ℝ) := by
    rw [show (8507101134224481029/8510000000000000000 : ℝ)+(198432233731/106375000000000 : ℝ)*((1483/10000 : ℝ)+(423/4000 : ℝ))=(10001332633305323/10000000000000000 : ℝ) by norm_num, show 1+(2158535660010721/5000000000000000000 : ℝ)+(10939502737010423/100000000000000000000 : ℝ)=(100054110215937224843/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2158535660010721/5000000000000000000 : ℝ) ≤ ((8507101134224481029/8510000000000000000 : ℝ)+2*(198432233731/106375000000000 : ℝ)*(1483/10000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (8507101134224481029/8510000000000000000 : ℝ)+2*(198432233731/106375000000000 : ℝ)*(1483/10000 : ℝ)=(10002126362240247/10000000000000000 : ℝ) by norm_num, show 1+2*(2158535660010721/5000000000000000000 : ℝ)=(2502158535660010721/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8507101134224481029/8510000000000000000 : ℝ)*(X 1 0+X 2 0)+(198432233731/106375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (423/4000 : ℝ)) (hi := (1483/10000 : ℝ)) (c := (8507101134224481029/8510000000000000000 : ℝ)) (alpha := (198432233731/106375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8507101134224481029/8510000000000000000 : ℝ)*(X 0 1+X 2 1)+(198432233731/106375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (423/4000 : ℝ)) (hi := (1483/10000 : ℝ)) (c := (8507101134224481029/8510000000000000000 : ℝ)) (alpha := (198432233731/106375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8507101134224481029/8510000000000000000 : ℝ)*(X 0 2+X 1 2)+(198432233731/106375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (423/4000 : ℝ)) (hi := (1483/10000 : ℝ)) (c := (8507101134224481029/8510000000000000000 : ℝ)) (alpha := (198432233731/106375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-27195319/125000000 : ℝ)*X 0 0+(675358407/1250000000 : ℝ)*X 0 1+(328531403/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347201001/10000000000 : ℝ)*X 1 0+(-2250021929/10000000000 : ℝ)*X 1 1+(5256502531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347200789/10000000000 : ℝ)*X 2 0+(5256502343/10000000000 : ℝ)*X 2 1+(-2250022459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1091749337/2500000000 : ℝ)*X 0 0+(4224380131/10000000000 : ℝ)*X 0 1+(1128607017/2500000000 : ℝ)*X 0 2+(1091749337/2500000000 : ℝ)*X 1 0+(4224380131/10000000000 : ℝ)*X 1 1+(1128607017/2500000000 : ℝ)*X 1 2+(1091749337/2500000000 : ℝ)*X 2 0+(4224380131/10000000000 : ℝ)*X 2 1+(1128607017/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2175632741/10000000000 : ℝ)*X 0 0+(1051384471/2000000000 : ℝ)*X 0 1+(2701222863/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531017589/1000000000 : ℝ)*X 1 0+(-2104079059/10000000000 : ℝ)*X 1 1+(1350611447/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265508797/500000000 : ℝ)*X 2 0+(2701222907/5000000000 : ℝ)*X 2 1+(-526019739/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873402457/2000000000 : ℝ)*X 0 0+(2256797769/5000000000 : ℝ)*X 0 1+(1056303943/2500000000 : ℝ)*X 0 2+(873402457/2000000000 : ℝ)*X 1 0+(2256797769/5000000000 : ℝ)*X 1 1+(1056303943/2500000000 : ℝ)*X 1 2+(873402457/2000000000 : ℝ)*X 2 0+(2256797769/5000000000 : ℝ)*X 2 1+(1056303943/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1532078030077007328539104803/425500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1289210283/100000000000000 : ℝ)*(base19) + (59626573/5000000000000 : ℝ)*(base23) + (136507889/100000000000000 : ℝ)*(upper2) + (69447811/25000000000000 : ℝ)*(upper3) + (5140033779711469/100000000000000 : ℝ)*(major0) + (5140033779711469/100000000000000 : ℝ)*(major1) + (5140033779711469/100000000000000 : ℝ)*(major2) + (1366457758415273/20000000000000 : ℝ)*(sp0) + (6832314256653721/100000000000000 : ℝ)*(sp1) + (6832302642566363/100000000000000 : ℝ)*(sp2) + (1723863868876371/50000000000000 : ℝ)*(sp3) + (26753787639/100000000000000 : ℝ)*(sp4) + (11710766183/100000000000000 : ℝ)*(sp6) + (6038946101/25000000000000 : ℝ)*(sp7) + (1723875946768573/50000000000000 : ℝ)*(f.failure) + (1708078886466001/25000000000000 : ℝ)*(f.sum) + (8443293969319/21275000000000000000000000000 : ℝ)*base66 + (7462902538762341601/851000000000000000000000000000000 : ℝ)*base67 + (5524269681326658399/851000000000000000000000000000000 : ℝ)*base70 + (5606043313224341601/851000000000000000000000000000000 : ℝ)*base71 + (115875718656519/21275000000000000000000000000 : ℝ)*base74 + (3630322731193658399/851000000000000000000000000000000 : ℝ)*base76 + (614020109581658399/851000000000000000000000000000000 : ℝ)*base78 + (7541778141523658399/851000000000000000000000000000000 : ℝ)*base80 + (154936193879869/21275000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base87 + (23065709/5000000000000000000000 : ℝ)*base89 + (23065709/5000000000000000000000 : ℝ)*base91 + (23065709/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (931152287012058388151237199/212750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143845079/20000000000000 : ℝ)*(base19) + (1015463177/100000000000000 : ℝ)*(base23) + (1318043/781250000000 : ℝ)*(upper3) + (2678289/3125000000000 : ℝ)*(lower4) + (15050489/10000000000000 : ℝ)*(upper5) + (5169698338638577/100000000000000 : ℝ)*(major0) + (5169698338638577/100000000000000 : ℝ)*(major1) + (5169698338638577/100000000000000 : ℝ)*(major2) + (700830939/5000000000000 : ℝ)*(sp1) + (6018942923/25000000000000 : ℝ)*(sp2) + (107371042289263/1562500000000 : ℝ)*(sp4) + (6871731970668657/100000000000000 : ℝ)*(sp5) + (1717930403819491/25000000000000 : ℝ)*(sp6) + (1733824912436423/50000000000000 : ℝ)*(sp7) + (1733824912436423/50000000000000 : ℝ)*(f.failure) + (107371042289263/1562500000000 : ℝ)*(f.sum) + (64505099620349/10637500000000000000000000000 : ℝ)*base65 + (3207037276820984267/851000000000000000000000000000000 : ℝ)*base68 + (7445155680056984267/851000000000000000000000000000000 : ℝ)*base70 + (5207117993132984267/851000000000000000000000000000000 : ℝ)*base72 + (50961411812227/21275000000000000000000000000 : ℝ)*base74 + (10068654957320984267/851000000000000000000000000000000 : ℝ)*base76 + (5464615491929015733/851000000000000000000000000000000 : ℝ)*base77 + (5721025472712984267/851000000000000000000000000000000 : ℝ)*base80 + (2714365745897/1329687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (27635241/5000000000000000000000 : ℝ)*base90 + (27635241/5000000000000000000000 : ℝ)*base92 + (27635241/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1122_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1483/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (423/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1122_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1122_s5_0 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2176309341/10000000000 : ℝ)*x 0 + (5395441341/10000000000 : ℝ)*x 1 + (5263479527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176309341/10000000000 : ℝ)^8315 ≤ (6610945953923/50000000000000 : ℝ)^6267 := by
    have hnat : (2176309341 : ℕ)^8315*50000000000000^6267 ≤ 6610945953923^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176309341 10000000000 6610945953923 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395441341/10000000000 : ℝ)^8315 ≤ (4410174443263/10000000000000 : ℝ)^6267 := by
    have hnat : (5395441341 : ℕ)^8315*10000000000000^6267 ≤ 4410174443263^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395441341 10000000000 4410174443263 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263479527/10000000000 : ℝ)^8315 ≤ (1707054545459/4000000000000 : ℝ)^6267 := by
    have hnat : (5263479527 : ℕ)^8315*4000000000000^6267 ≤ 1707054545459^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263479527 10000000000 1707054545459 4000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2176309341/10000000000 : ℝ), (5395441341/10000000000 : ℝ), (5263479527/10000000000 : ℝ)] ![(6610945953923/50000000000000 : ℝ), (4410174443263/10000000000000 : ℝ), (1707054545459/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2176309341/10000000000 : ℝ)|^8315 ≤ (6610945953923/50000000000000 : ℝ)^6267
        have hw : |(-2176309341/10000000000 : ℝ)|=(2176309341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395441341/10000000000 : ℝ)|^8315 ≤ (4410174443263/10000000000000 : ℝ)^6267
        have hw : |(5395441341/10000000000 : ℝ)|=(5395441341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263479527/10000000000 : ℝ)|^8315 ≤ (1707054545459/4000000000000 : ℝ)^6267
        have hw : |(5263479527/10000000000 : ℝ)|=(5263479527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s5_1 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345341747/10000000000 : ℝ)*x 0 + (-2243277507/10000000000 : ℝ)*x 1 + (2631739619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345341747/10000000000 : ℝ)^8315 ≤ (21779619083283/50000000000000 : ℝ)^6267 := by
    have hnat : (5345341747 : ℕ)^8315*50000000000000^6267 ≤ 21779619083283^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345341747 10000000000 21779619083283 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243277507/10000000000 : ℝ)^8315 ≤ (107534385073/781250000000 : ℝ)^6267 := by
    have hnat : (2243277507 : ℕ)^8315*781250000000^6267 ≤ 107534385073^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243277507 10000000000 107534385073 781250000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631739619/5000000000 : ℝ)^8315 ≤ (42676360527517/100000000000000 : ℝ)^6267 := by
    have hnat : (2631739619 : ℕ)^8315*100000000000000^6267 ≤ 42676360527517^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631739619 5000000000 42676360527517 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345341747/10000000000 : ℝ), (-2243277507/10000000000 : ℝ), (2631739619/5000000000 : ℝ)] ![(21779619083283/50000000000000 : ℝ), (107534385073/781250000000 : ℝ), (42676360527517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345341747/10000000000 : ℝ)|^8315 ≤ (21779619083283/50000000000000 : ℝ)^6267
        have hw : |(5345341747/10000000000 : ℝ)|=(5345341747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2243277507/10000000000 : ℝ)|^8315 ≤ (107534385073/781250000000 : ℝ)^6267
        have hw : |(-2243277507/10000000000 : ℝ)|=(2243277507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631739619/5000000000 : ℝ)|^8315 ≤ (42676360527517/100000000000000 : ℝ)^6267
        have hw : |(2631739619/5000000000 : ℝ)|=(2631739619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s5_2 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345341453/10000000000 : ℝ)*x 0 + (105269589/200000000 : ℝ)*x 1 + (-1121638809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345341453/10000000000 : ℝ)^8315 ≤ (10889808746957/25000000000000 : ℝ)^6267 := by
    have hnat : (5345341453 : ℕ)^8315*25000000000000^6267 ≤ 10889808746957^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345341453 10000000000 10889808746957 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105269589/200000000 : ℝ)^8315 ≤ (42676362808137/100000000000000 : ℝ)^6267 := by
    have hnat : (105269589 : ℕ)^8315*100000000000000^6267 ≤ 42676362808137^6267*200000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105269589 200000000 42676362808137 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121638809/5000000000 : ℝ)^8315 ≤ (6882201096497/50000000000000 : ℝ)^6267 := by
    have hnat : (1121638809 : ℕ)^8315*50000000000000^6267 ≤ 6882201096497^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121638809 5000000000 6882201096497 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345341453/10000000000 : ℝ), (105269589/200000000 : ℝ), (-1121638809/5000000000 : ℝ)] ![(10889808746957/25000000000000 : ℝ), (42676362808137/100000000000000 : ℝ), (6882201096497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345341453/10000000000 : ℝ)|^8315 ≤ (10889808746957/25000000000000 : ℝ)^6267
        have hw : |(5345341453/10000000000 : ℝ)|=(5345341453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105269589/200000000 : ℝ)|^8315 ≤ (42676362808137/100000000000000 : ℝ)^6267
        have hw : |(105269589/200000000 : ℝ)|=(105269589/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1121638809/5000000000 : ℝ)|^8315 ≤ (6882201096497/50000000000000 : ℝ)^6267
        have hw : |(-1121638809/5000000000 : ℝ)|=(1121638809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s5_3 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183697659/5000000000 : ℝ)*x 0 + (4238599613/10000000000 : ℝ)*x 1 + (112502627/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183697659/5000000000 : ℝ)^8315 ≤ (16657906296907/50000000000000 : ℝ)^6267 := by
    have hnat : (2183697659 : ℕ)^8315*50000000000000^6267 ≤ 16657906296907^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183697659 5000000000 16657906296907 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238599613/10000000000 : ℝ)^8315 ≤ (32018573541769/100000000000000 : ℝ)^6267 := by
    have hnat : (4238599613 : ℕ)^8315*100000000000000^6267 ≤ 32018573541769^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238599613 10000000000 32018573541769 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112502627/250000000 : ℝ)^8315 ≤ (34665613859929/100000000000000 : ℝ)^6267 := by
    have hnat : (112502627 : ℕ)^8315*100000000000000^6267 ≤ 34665613859929^6267*250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112502627 250000000 34665613859929 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183697659/5000000000 : ℝ), (4238599613/10000000000 : ℝ), (112502627/250000000 : ℝ)] ![(16657906296907/50000000000000 : ℝ), (32018573541769/100000000000000 : ℝ), (34665613859929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183697659/5000000000 : ℝ)|^8315 ≤ (16657906296907/50000000000000 : ℝ)^6267
        have hw : |(2183697659/5000000000 : ℝ)|=(2183697659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238599613/10000000000 : ℝ)|^8315 ≤ (32018573541769/100000000000000 : ℝ)^6267
        have hw : |(4238599613/10000000000 : ℝ)|=(4238599613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112502627/250000000 : ℝ)|^8315 ≤ (34665613859929/100000000000000 : ℝ)^6267
        have hw : |(112502627/250000000 : ℝ)|=(112502627/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s5_4 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1088157191/5000000000 : ℝ)*x 0 + (164494409/312500000 : ℝ)*x 1 + (269754939/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088157191/5000000000 : ℝ)^8315 ≤ (1322193254211/10000000000000 : ℝ)^6267 := by
    have hnat : (1088157191 : ℕ)^8315*10000000000000^6267 ≤ 1322193254211^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088157191 5000000000 1322193254211 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164494409/312500000 : ℝ)^8315 ≤ (4268003806589/10000000000000 : ℝ)^6267 := by
    have hnat : (164494409 : ℕ)^8315*10000000000000^6267 ≤ 4268003806589^6267*312500000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164494409 312500000 4268003806589 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269754939/500000000 : ℝ)^8315 ≤ (5512253672721/12500000000000 : ℝ)^6267 := by
    have hnat : (269754939 : ℕ)^8315*12500000000000^6267 ≤ 5512253672721^6267*500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269754939 500000000 5512253672721 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1088157191/5000000000 : ℝ), (164494409/312500000 : ℝ), (269754939/500000000 : ℝ)] ![(1322193254211/10000000000000 : ℝ), (4268003806589/10000000000000 : ℝ), (5512253672721/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1088157191/5000000000 : ℝ)|^8315 ≤ (1322193254211/10000000000000 : ℝ)^6267
        have hw : |(-1088157191/5000000000 : ℝ)|=(1088157191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164494409/312500000 : ℝ)|^8315 ≤ (4268003806589/10000000000000 : ℝ)^6267
        have hw : |(164494409/312500000 : ℝ)|=(164494409/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269754939/500000000 : ℝ)|^8315 ≤ (5512253672721/12500000000000 : ℝ)^6267
        have hw : |(269754939/500000000 : ℝ)|=(269754939/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s5_5 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311958797/10000000000 : ℝ)*x 0 + (-422331641/2000000000 : ℝ)*x 1 + (5395098719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311958797/10000000000 : ℝ)^8315 ≤ (43198669447747/100000000000000 : ℝ)^6267 := by
    have hnat : (5311958797 : ℕ)^8315*100000000000000^6267 ≤ 43198669447747^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311958797 10000000000 43198669447747 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422331641/2000000000 : ℝ)^8315 ≤ (12703301813929/100000000000000 : ℝ)^6267 := by
    have hnat : (422331641 : ℕ)^8315*100000000000000^6267 ≤ 12703301813929^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422331641 2000000000 12703301813929 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395098719/10000000000 : ℝ)^8315 ≤ (22049014360117/50000000000000 : ℝ)^6267 := by
    have hnat : (5395098719 : ℕ)^8315*50000000000000^6267 ≤ 22049014360117^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395098719 10000000000 22049014360117 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311958797/10000000000 : ℝ), (-422331641/2000000000 : ℝ), (5395098719/10000000000 : ℝ)] ![(43198669447747/100000000000000 : ℝ), (12703301813929/100000000000000 : ℝ), (22049014360117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311958797/10000000000 : ℝ)|^8315 ≤ (43198669447747/100000000000000 : ℝ)^6267
        have hw : |(5311958797/10000000000 : ℝ)|=(5311958797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422331641/2000000000 : ℝ)|^8315 ≤ (12703301813929/100000000000000 : ℝ)^6267
        have hw : |(-422331641/2000000000 : ℝ)|=(422331641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395098719/10000000000 : ℝ)|^8315 ≤ (22049014360117/50000000000000 : ℝ)^6267
        have hw : |(5395098719/10000000000 : ℝ)|=(5395098719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s5_6 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311958769/10000000000 : ℝ)*x 0 + (2697549377/5000000000 : ℝ)*x 1 + (-422331639/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311958769/10000000000 : ℝ)^8315 ≤ (43198669145629/100000000000000 : ℝ)^6267 := by
    have hnat : (5311958769 : ℕ)^8315*100000000000000^6267 ≤ 43198669145629^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311958769 10000000000 43198669145629 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697549377/5000000000 : ℝ)^8315 ≤ (44098029099803/100000000000000 : ℝ)^6267 := by
    have hnat : (2697549377 : ℕ)^8315*100000000000000^6267 ≤ 44098029099803^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697549377 5000000000 44098029099803 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422331639/2000000000 : ℝ)^8315 ≤ (396978179191/3125000000000 : ℝ)^6267 := by
    have hnat : (422331639 : ℕ)^8315*3125000000000^6267 ≤ 396978179191^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422331639 2000000000 396978179191 3125000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311958769/10000000000 : ℝ), (2697549377/5000000000 : ℝ), (-422331639/2000000000 : ℝ)] ![(43198669145629/100000000000000 : ℝ), (44098029099803/100000000000000 : ℝ), (396978179191/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311958769/10000000000 : ℝ)|^8315 ≤ (43198669145629/100000000000000 : ℝ)^6267
        have hw : |(5311958769/10000000000 : ℝ)|=(5311958769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697549377/5000000000 : ℝ)|^8315 ≤ (44098029099803/100000000000000 : ℝ)^6267
        have hw : |(2697549377/5000000000 : ℝ)|=(2697549377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422331639/2000000000 : ℝ)|^8315 ≤ (396978179191/3125000000000 : ℝ)^6267
        have hw : |(-422331639/2000000000 : ℝ)|=(422331639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s5_7 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367406201/10000000000 : ℝ)*x 0 + (4499428261/10000000000 : ℝ)*x 1 + (2119639389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367406201/10000000000 : ℝ)^8315 ≤ (33315922742487/100000000000000 : ℝ)^6267 := by
    have hnat : (4367406201 : ℕ)^8315*100000000000000^6267 ≤ 33315922742487^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367406201 10000000000 33315922742487 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499428261/10000000000 : ℝ)^8315 ≤ (17329348247659/50000000000000 : ℝ)^6267 := by
    have hnat : (4499428261 : ℕ)^8315*50000000000000^6267 ≤ 17329348247659^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499428261 10000000000 17329348247659 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119639389/5000000000 : ℝ)^8315 ≤ (16012690373241/50000000000000 : ℝ)^6267 := by
    have hnat : (2119639389 : ℕ)^8315*50000000000000^6267 ≤ 16012690373241^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119639389 5000000000 16012690373241 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367406201/10000000000 : ℝ), (4499428261/10000000000 : ℝ), (2119639389/5000000000 : ℝ)] ![(33315922742487/100000000000000 : ℝ), (17329348247659/50000000000000 : ℝ), (16012690373241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367406201/10000000000 : ℝ)|^8315 ≤ (33315922742487/100000000000000 : ℝ)^6267
        have hw : |(4367406201/10000000000 : ℝ)|=(4367406201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499428261/10000000000 : ℝ)|^8315 ≤ (17329348247659/50000000000000 : ℝ)^6267
        have hw : |(4499428261/10000000000 : ℝ)|=(4499428261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119639389/5000000000 : ℝ)|^8315 ≤ (16012690373241/50000000000000 : ℝ)^6267
        have hw : |(2119639389/5000000000 : ℝ)|=(2119639389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1122_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5643/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11137/100000 : ℝ) ^ (4157/1024 : ℝ) ≤ (6749297441828589/50000000000000000000 : ℝ) := by
    have hpowers : (11137/100000 : ℝ)^4157 ≤ (6749297441828589/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11137 : ℕ)^4157*50000000000000000000^1024 ≤ 6749297441828589^1024*100000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11137 100000 6749297441828589 50000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11137/100000 : ℝ)) (X := (6749297441828589/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (4157/1024 : ℝ) ≤ (36569495978747207/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^4157 ≤ (36569495978747207/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3559 : ℕ)^4157*100000000000000000000^1024 ≤ 36569495978747207^1024*25000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 36569495978747207 100000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (36569495978747207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006749297441828589/25000000000000000000 : ℝ) ≤ (1000066495815007/1000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (25006749297441828589/25000000000000000000 : ℝ)^1024 ≤ (1000066495815007/1000000000000000 : ℝ)^4157 := by
      have hnat : (25006749297441828589 : ℕ)^1024*1000000000000000^4157 ≤ 1000066495815007^4157*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006749297441828589 25000000000000000000 1000066495815007 1000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000066495815007/1000000000000000 : ℝ)) (X := (25006749297441828589/25000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010013618172480877/20000000000000000000 : ℝ) ≤ (5000616551053929/5000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (20010013618172480877/20000000000000000000 : ℝ)^1024 ≤ (5000616551053929/5000000000000000 : ℝ)^4157 := by
      have hnat : (20010013618172480877 : ℕ)^1024*5000000000000000^4157 ≤ 5000616551053929^4157*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010013618172480877 20000000000000000000 5000616551053929 5000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000616551053929/5000000000000000 : ℝ)) (X := (20010013618172480877/20000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036569495978747207/50000000000000000000 : ℝ) ≤ (5000900623032823/5000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (50036569495978747207/50000000000000000000 : ℝ)^1024 ≤ (5000900623032823/5000000000000000 : ℝ)^4157 := by
      have hnat : (50036569495978747207 : ℕ)^1024*5000000000000000^4157 ≤ 5000900623032823^4157*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036569495978747207 50000000000000000000 5000900623032823 5000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000900623032823/5000000000000000 : ℝ)) (X := (50036569495978747207/50000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6749297441828589/50000000000000000000 : ℝ) ≤ ((15489702933395648509/15495000000000000000 : ℝ)+2*(142035989447/77475000000000 : ℝ)*(11137/100000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (15489702933395648509/15495000000000000000 : ℝ)+2*(142035989447/77475000000000 : ℝ)*(11137/100000 : ℝ)=(1000066495815007/1000000000000000 : ℝ) by norm_num, show 1+2*(6749297441828589/50000000000000000000 : ℝ)=(25006749297441828589/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36569495978747207/100000000000000000000 : ℝ)+(6749297441828589/50000000000000000000 : ℝ) ≤ ((15489702933395648509/15495000000000000000 : ℝ)+(142035989447/77475000000000 : ℝ)*((3559/25000 : ℝ)+(11137/100000 : ℝ)))^(4157/1024 : ℝ) := by
    rw [show (15489702933395648509/15495000000000000000 : ℝ)+(142035989447/77475000000000 : ℝ)*((3559/25000 : ℝ)+(11137/100000 : ℝ))=(5000616551053929/5000000000000000 : ℝ) by norm_num, show 1+(36569495978747207/100000000000000000000 : ℝ)+(6749297441828589/50000000000000000000 : ℝ)=(20010013618172480877/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36569495978747207/100000000000000000000 : ℝ) ≤ ((15489702933395648509/15495000000000000000 : ℝ)+2*(142035989447/77475000000000 : ℝ)*(3559/25000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (15489702933395648509/15495000000000000000 : ℝ)+2*(142035989447/77475000000000 : ℝ)*(3559/25000 : ℝ)=(5000900623032823/5000000000000000 : ℝ) by norm_num, show 1+2*(36569495978747207/100000000000000000000 : ℝ)=(50036569495978747207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15489702933395648509/15495000000000000000 : ℝ)*(X 1 0+X 2 0)+(142035989447/77475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (15489702933395648509/15495000000000000000 : ℝ)) (alpha := (142035989447/77475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15489702933395648509/15495000000000000000 : ℝ)*(X 0 1+X 2 1)+(142035989447/77475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (15489702933395648509/15495000000000000000 : ℝ)) (alpha := (142035989447/77475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15489702933395648509/15495000000000000000 : ℝ)*(X 0 2+X 1 2)+(142035989447/77475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (15489702933395648509/15495000000000000000 : ℝ)) (alpha := (142035989447/77475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2176309341/10000000000 : ℝ)*X 0 0+(5395441341/10000000000 : ℝ)*X 0 1+(5263479527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345341747/10000000000 : ℝ)*X 1 0+(-2243277507/10000000000 : ℝ)*X 1 1+(2631739619/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345341453/10000000000 : ℝ)*X 2 0+(105269589/200000000 : ℝ)*X 2 1+(-1121638809/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183697659/5000000000 : ℝ)*X 0 0+(4238599613/10000000000 : ℝ)*X 0 1+(112502627/250000000 : ℝ)*X 0 2+(2183697659/5000000000 : ℝ)*X 1 0+(4238599613/10000000000 : ℝ)*X 1 1+(112502627/250000000 : ℝ)*X 1 2+(2183697659/5000000000 : ℝ)*X 2 0+(4238599613/10000000000 : ℝ)*X 2 1+(112502627/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1088157191/5000000000 : ℝ)*X 0 0+(164494409/312500000 : ℝ)*X 0 1+(269754939/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311958797/10000000000 : ℝ)*X 1 0+(-422331641/2000000000 : ℝ)*X 1 1+(5395098719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311958769/10000000000 : ℝ)*X 2 0+(2697549377/5000000000 : ℝ)*X 2 1+(-422331639/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367406201/10000000000 : ℝ)*X 0 0+(4499428261/10000000000 : ℝ)*X 0 1+(2119639389/5000000000 : ℝ)*X 0 2+(4367406201/10000000000 : ℝ)*X 1 0+(4499428261/10000000000 : ℝ)*X 1 1+(2119639389/5000000000 : ℝ)*X 1 2+(4367406201/10000000000 : ℝ)*X 2 0+(4499428261/10000000000 : ℝ)*X 2 1+(2119639389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53264025541639609585488747/64562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (240972231/25000000000000 : ℝ)*(base19) + (128639087/20000000000000 : ℝ)*(base23) + (4487737/2500000000000 : ℝ)*(upper2) + (45069379/25000000000000 : ℝ)*(upper3) + (128138731/100000000000000 : ℝ)*(upper4) + (1425250170050083/25000000000000 : ℝ)*(major0) + (1425250170050083/25000000000000 : ℝ)*(major1) + (1425250170050083/25000000000000 : ℝ)*(major2) + (3788984219019423/50000000000000 : ℝ)*(sp0) + (378898591255681/5000000000000 : ℝ)*(sp1) + (7577972145807109/100000000000000 : ℝ)*(sp2) + (956004925505153/25000000000000 : ℝ)*(sp3) + (2175481849/50000000000000 : ℝ)*(sp4) + (4420938759/50000000000000 : ℝ)*(sp7) + (382402854389813/10000000000000 : ℝ)*(f.failure) + (473623299312659/6250000000000 : ℝ)*(f.sum) + (26086720798169/3873750000000000000000000000 : ℝ)*base65 + (4389505449777523753/387375000000000000000000000000000 : ℝ)*base68 + (1223457202320226247/387375000000000000000000000000000 : ℝ)*base69 + (762018495826273753/387375000000000000000000000000000 : ℝ)*base72 + (24291248780657/7747500000000000000000000000 : ℝ)*base74 + (3814442714495023753/387375000000000000000000000000000 : ℝ)*base76 + (9357961536740851247/387375000000000000000000000000000 : ℝ)*base77 + (11578493652260023753/387375000000000000000000000000000 : ℝ)*base80 + (2815346033687/7747500000000000000000000000 : ℝ)*base82 + (230629/1000000000000000000000 : ℝ)*base89 + (230629/1000000000000000000000 : ℝ)*base91 + (230629/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53515772122808929539669667/5165000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115395059/6250000000000 : ℝ)*(base19) + (2040832781/100000000000000 : ℝ)*(base23) + (182739631/100000000000000 : ℝ)*(upper3) + (103303803/100000000000000 : ℝ)*(lower4) + (41330641/25000000000000 : ℝ)*(upper5) + (229227603055463/4000000000000 : ℝ)*(major0) + (229227603055463/4000000000000 : ℝ)*(major1) + (229227603055463/4000000000000 : ℝ)*(major2) + (9436393003/20000000000000 : ℝ)*(sp1) + (53577542959/100000000000000 : ℝ)*(sp2) + (304697466888583/4000000000000 : ℝ)*(sp4) + (952173455491077/12500000000000 : ℝ)*(sp5) + (3808690526919417/50000000000000 : ℝ)*(sp6) + (240246445949007/6250000000000 : ℝ)*(sp7) + (240246445949007/6250000000000 : ℝ)*(f.failure) + (304697466888583/4000000000000 : ℝ)*(f.sum) + (6830020866059/1549500000000000000000000000 : ℝ)*base66 + (522266740074905333/61980000000000000000000000000000 : ℝ)*base68 + (278713032986825333/61980000000000000000000000000000 : ℝ)*base70 + (260360819012165333/61980000000000000000000000000000 : ℝ)*base72 + (12689795919133/3099000000000000000000000000 : ℝ)*base74 + (630956086284654667/61980000000000000000000000000000 : ℝ)*base75 + (163411617231845333/61980000000000000000000000000000 : ℝ)*base78 + (80532043851185333/61980000000000000000000000000000 : ℝ)*base80 + (132815512487/24210937500000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2552431/625000000000000000000 : ℝ)*base89 + (2552431/625000000000000000000 : ℝ)*base91 + (2552431/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1122_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1122_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1122_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16563/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1122_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1122_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1122_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16563/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1122_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
