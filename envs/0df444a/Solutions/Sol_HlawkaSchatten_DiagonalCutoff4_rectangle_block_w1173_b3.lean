-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1173_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:46:44.408233+00:00
-- url     : https://prove2.me/submissions/4077d290-87a5-4e58-b141-a4b9cf850966

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
theorem support_rectangle_w1173_box_0 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-101313733/500000000 : ℝ)*x 0 + (2687931187/5000000000 : ℝ)*x 1 + (2687931291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101313733/500000000 : ℝ)^4183 ≤ (12077091146363/100000000000000 : ℝ)^3159 := by
    have hnat : (101313733 : ℕ)^4183*100000000000000^3159 ≤ 12077091146363^3159*500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101313733 500000000 12077091146363 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687931187/5000000000 : ℝ)^4183 ≤ (2198072664709/5000000000000 : ℝ)^3159 := by
    have hnat : (2687931187 : ℕ)^4183*5000000000000^3159 ≤ 2198072664709^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687931187 5000000000 2198072664709 5000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687931291/5000000000 : ℝ)^4183 ≤ (10990363886619/25000000000000 : ℝ)^3159 := by
    have hnat : (2687931291 : ℕ)^4183*25000000000000^3159 ≤ 10990363886619^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687931291 5000000000 10990363886619 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-101313733/500000000 : ℝ), (2687931187/5000000000 : ℝ), (2687931291/5000000000 : ℝ)] ![(12077091146363/100000000000000 : ℝ), (2198072664709/5000000000000 : ℝ), (10990363886619/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-101313733/500000000 : ℝ)|^4183 ≤ (12077091146363/100000000000000 : ℝ)^3159
        have hw : |(-101313733/500000000 : ℝ)|=(101313733/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687931187/5000000000 : ℝ)|^4183 ≤ (2198072664709/5000000000000 : ℝ)^3159
        have hw : |(2687931187/5000000000 : ℝ)|=(2687931187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687931291/5000000000 : ℝ)|^4183 ≤ (10990363886619/25000000000000 : ℝ)^3159
        have hw : |(2687931291/5000000000 : ℝ)|=(2687931291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_1 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296262269/10000000000 : ℝ)*x 0 + (-1067150841/5000000000 : ℝ)*x 1 + (167995713/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296262269/10000000000 : ℝ)^4183 ≤ (21550795630619/50000000000000 : ℝ)^3159 := by
    have hnat : (5296262269 : ℕ)^4183*50000000000000^3159 ≤ 21550795630619^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296262269 10000000000 21550795630619 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1067150841/5000000000 : ℝ)^4183 ≤ (6468475321463/50000000000000 : ℝ)^3159 := by
    have hnat : (1067150841 : ℕ)^4183*50000000000000^3159 ≤ 6468475321463^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067150841 5000000000 6468475321463 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (167995713/312500000 : ℝ)^4183 ≤ (43961458080309/100000000000000 : ℝ)^3159 := by
    have hnat : (167995713 : ℕ)^4183*100000000000000^3159 ≤ 43961458080309^3159*312500000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167995713 312500000 43961458080309 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296262269/10000000000 : ℝ), (-1067150841/5000000000 : ℝ), (167995713/312500000 : ℝ)] ![(21550795630619/50000000000000 : ℝ), (6468475321463/50000000000000 : ℝ), (43961458080309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296262269/10000000000 : ℝ)|^4183 ≤ (21550795630619/50000000000000 : ℝ)^3159
        have hw : |(5296262269/10000000000 : ℝ)|=(5296262269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1067150841/5000000000 : ℝ)|^4183 ≤ (6468475321463/50000000000000 : ℝ)^3159
        have hw : |(-1067150841/5000000000 : ℝ)|=(1067150841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(167995713/312500000 : ℝ)|^4183 ≤ (43961458080309/100000000000000 : ℝ)^3159
        have hw : |(167995713/312500000 : ℝ)|=(167995713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_2 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296261901/10000000000 : ℝ)*x 0 + (5375862981/10000000000 : ℝ)*x 1 + (-2134301953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296261901/10000000000 : ℝ)^4183 ≤ (43101587295629/100000000000000 : ℝ)^3159 := by
    have hnat : (5296261901 : ℕ)^4183*100000000000000^3159 ≤ 43101587295629^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296261901 10000000000 43101587295629 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375862981/10000000000 : ℝ)^4183 ≤ (21980729933493/50000000000000 : ℝ)^3159 := by
    have hnat : (5375862981 : ℕ)^4183*50000000000000^3159 ≤ 21980729933493^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375862981 10000000000 21980729933493 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2134301953/10000000000 : ℝ)^4183 ≤ (101069943891/781250000000 : ℝ)^3159 := by
    have hnat : (2134301953 : ℕ)^4183*781250000000^3159 ≤ 101069943891^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134301953 10000000000 101069943891 781250000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296261901/10000000000 : ℝ), (5375862981/10000000000 : ℝ), (-2134301953/10000000000 : ℝ)] ![(43101587295629/100000000000000 : ℝ), (21980729933493/50000000000000 : ℝ), (101069943891/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296261901/10000000000 : ℝ)|^4183 ≤ (43101587295629/100000000000000 : ℝ)^3159
        have hw : |(5296261901/10000000000 : ℝ)|=(5296261901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375862981/10000000000 : ℝ)|^4183 ≤ (21980729933493/50000000000000 : ℝ)^3159
        have hw : |(5375862981/10000000000 : ℝ)|=(5375862981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2134301953/10000000000 : ℝ)|^4183 ≤ (101069943891/781250000000 : ℝ)^3159
        have hw : |(-2134301953/10000000000 : ℝ)|=(2134301953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_3 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4467542591/10000000000 : ℝ)*x 0 + (430880527/1000000000 : ℝ)*x 1 + (34470441/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4467542591/10000000000 : ℝ)^4183 ≤ (34406250484263/100000000000000 : ℝ)^3159 := by
    have hnat : (4467542591 : ℕ)^4183*100000000000000^3159 ≤ 34406250484263^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4467542591 10000000000 34406250484263 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430880527/1000000000 : ℝ)^4183 ≤ (16398437739199/50000000000000 : ℝ)^3159 := by
    have hnat : (430880527 : ℕ)^4183*50000000000000^3159 ≤ 16398437739199^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430880527 1000000000 16398437739199 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34470441/80000000 : ℝ)^4183 ≤ (6559374803391/20000000000000 : ℝ)^3159 := by
    have hnat : (34470441 : ℕ)^4183*20000000000000^3159 ≤ 6559374803391^3159*80000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34470441 80000000 6559374803391 20000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4467542591/10000000000 : ℝ), (430880527/1000000000 : ℝ), (34470441/80000000 : ℝ)] ![(34406250484263/100000000000000 : ℝ), (16398437739199/50000000000000 : ℝ), (6559374803391/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4467542591/10000000000 : ℝ)|^4183 ≤ (34406250484263/100000000000000 : ℝ)^3159
        have hw : |(4467542591/10000000000 : ℝ)|=(4467542591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(430880527/1000000000 : ℝ)|^4183 ≤ (16398437739199/50000000000000 : ℝ)^3159
        have hw : |(430880527/1000000000 : ℝ)|=(430880527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34470441/80000000 : ℝ)|^4183 ≤ (6559374803391/20000000000000 : ℝ)^3159
        have hw : |(34470441/80000000 : ℝ)|=(34470441/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_4 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-455882609/2000000000 : ℝ)*x 0 + (5281524263/10000000000 : ℝ)*x 1 + (1320381351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (455882609/2000000000 : ℝ)^4183 ≤ (1764287324879/12500000000000 : ℝ)^3159 := by
    have hnat : (455882609 : ℕ)^4183*12500000000000^3159 ≤ 1764287324879^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455882609 2000000000 1764287324879 12500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281524263/10000000000 : ℝ)^4183 ≤ (2683927784099/6250000000000 : ℝ)^3159 := by
    have hnat : (5281524263 : ℕ)^4183*6250000000000^3159 ≤ 2683927784099^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281524263 10000000000 2683927784099 6250000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320381351/2500000000 : ℝ)^4183 ≤ (21471428415013/50000000000000 : ℝ)^3159 := by
    have hnat : (1320381351 : ℕ)^4183*50000000000000^3159 ≤ 21471428415013^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320381351 2500000000 21471428415013 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-455882609/2000000000 : ℝ), (5281524263/10000000000 : ℝ), (1320381351/2500000000 : ℝ)] ![(1764287324879/12500000000000 : ℝ), (2683927784099/6250000000000 : ℝ), (21471428415013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-455882609/2000000000 : ℝ)|^4183 ≤ (1764287324879/12500000000000 : ℝ)^3159
        have hw : |(-455882609/2000000000 : ℝ)|=(455882609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281524263/10000000000 : ℝ)|^4183 ≤ (2683927784099/6250000000000 : ℝ)^3159
        have hw : |(5281524263/10000000000 : ℝ)|=(5281524263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320381351/2500000000 : ℝ)|^4183 ≤ (21471428415013/50000000000000 : ℝ)^3159
        have hw : |(1320381351/2500000000 : ℝ)|=(1320381351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_5 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681432849/5000000000 : ℝ)*x 0 + (-434300477/2000000000 : ℝ)*x 1 + (5281524759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681432849/5000000000 : ℝ)^4183 ≤ (2738798497463/6250000000000 : ℝ)^3159 := by
    have hnat : (2681432849 : ℕ)^4183*6250000000000^3159 ≤ 2738798497463^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681432849 5000000000 2738798497463 6250000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434300477/2000000000 : ℝ)^4183 ≤ (13236374138027/100000000000000 : ℝ)^3159 := by
    have hnat : (434300477 : ℕ)^4183*100000000000000^3159 ≤ 13236374138027^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434300477 2000000000 13236374138027 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281524759/10000000000 : ℝ)^4183 ≤ (42942849885709/100000000000000 : ℝ)^3159 := by
    have hnat : (5281524759 : ℕ)^4183*100000000000000^3159 ≤ 42942849885709^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281524759 10000000000 42942849885709 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681432849/5000000000 : ℝ), (-434300477/2000000000 : ℝ), (5281524759/10000000000 : ℝ)] ![(2738798497463/6250000000000 : ℝ), (13236374138027/100000000000000 : ℝ), (42942849885709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681432849/5000000000 : ℝ)|^4183 ≤ (2738798497463/6250000000000 : ℝ)^3159
        have hw : |(2681432849/5000000000 : ℝ)|=(2681432849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434300477/2000000000 : ℝ)|^4183 ≤ (13236374138027/100000000000000 : ℝ)^3159
        have hw : |(-434300477/2000000000 : ℝ)|=(434300477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281524759/10000000000 : ℝ)|^4183 ≤ (42942849885709/100000000000000 : ℝ)^3159
        have hw : |(5281524759/10000000000 : ℝ)|=(5281524759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_6 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681432869/5000000000 : ℝ)*x 0 + (330095289/625000000 : ℝ)*x 1 + (-2171502513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681432869/5000000000 : ℝ)^4183 ≤ (43820776392203/100000000000000 : ℝ)^3159 := by
    have hnat : (2681432869 : ℕ)^4183*100000000000000^3159 ≤ 43820776392203^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681432869 5000000000 43820776392203 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330095289/625000000 : ℝ)^4183 ≤ (5367856054031/12500000000000 : ℝ)^3159 := by
    have hnat : (330095289 : ℕ)^4183*12500000000000^3159 ≤ 5367856054031^3159*625000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330095289 625000000 5367856054031 12500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2171502513/10000000000 : ℝ)^4183 ≤ (6618187585581/50000000000000 : ℝ)^3159 := by
    have hnat : (2171502513 : ℕ)^4183*50000000000000^3159 ≤ 6618187585581^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171502513 10000000000 6618187585581 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681432869/5000000000 : ℝ), (330095289/625000000 : ℝ), (-2171502513/10000000000 : ℝ)] ![(43820776392203/100000000000000 : ℝ), (5367856054031/12500000000000 : ℝ), (6618187585581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681432869/5000000000 : ℝ)|^4183 ≤ (43820776392203/100000000000000 : ℝ)^3159
        have hw : |(2681432869/5000000000 : ℝ)|=(2681432869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(330095289/625000000 : ℝ)|^4183 ≤ (5367856054031/12500000000000 : ℝ)^3159
        have hw : |(330095289/625000000 : ℝ)|=(330095289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2171502513/10000000000 : ℝ)|^4183 ≤ (6618187585581/50000000000000 : ℝ)^3159
        have hw : |(-2171502513/10000000000 : ℝ)|=(2171502513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_7 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531592037/1250000000 : ℝ)*x 0 + (4416187981/10000000000 : ℝ)*x 1 + (4416187511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531592037/1250000000 : ℝ)^4183 ≤ (6446591268647/20000000000000 : ℝ)^3159 := by
    have hnat : (531592037 : ℕ)^4183*20000000000000^3159 ≤ 6446591268647^3159*1250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531592037 1250000000 6446591268647 20000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4416187981/10000000000 : ℝ)^4183 ≤ (16941762104563/50000000000000 : ℝ)^3159 := by
    have hnat : (4416187981 : ℕ)^4183*50000000000000^3159 ≤ 16941762104563^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416187981 10000000000 16941762104563 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4416187511/10000000000 : ℝ)^4183 ≤ (6776703886817/20000000000000 : ℝ)^3159 := by
    have hnat : (4416187511 : ℕ)^4183*20000000000000^3159 ≤ 6776703886817^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416187511 10000000000 6776703886817 20000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531592037/1250000000 : ℝ), (4416187981/10000000000 : ℝ), (4416187511/10000000000 : ℝ)] ![(6446591268647/20000000000000 : ℝ), (16941762104563/50000000000000 : ℝ), (6776703886817/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531592037/1250000000 : ℝ)|^4183 ≤ (6446591268647/20000000000000 : ℝ)^3159
        have hw : |(531592037/1250000000 : ℝ)|=(531592037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4416187981/10000000000 : ℝ)|^4183 ≤ (16941762104563/50000000000000 : ℝ)^3159
        have hw : |(4416187981/10000000000 : ℝ)|=(4416187981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4416187511/10000000000 : ℝ)|^4183 ≤ (6776703886817/20000000000000 : ℝ)^3159
        have hw : |(4416187511/10000000000 : ℝ)|=(4416187511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_8 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-445288589/2000000000 : ℝ)*x 0 + (2608653227/5000000000 : ℝ)*x 1 + (2692736703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445288589/2000000000 : ℝ)^4183 ≤ (13681627585093/100000000000000 : ℝ)^3159 := by
    have hnat : (445288589 : ℕ)^4183*100000000000000^3159 ≤ 13681627585093^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445288589 2000000000 13681627585093 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608653227/5000000000 : ℝ)^4183 ≤ (21126408688523/50000000000000 : ℝ)^3159 := by
    have hnat : (2608653227 : ℕ)^4183*50000000000000^3159 ≤ 21126408688523^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608653227 5000000000 21126408688523 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692736703/5000000000 : ℝ)^4183 ≤ (44065555021211/100000000000000 : ℝ)^3159 := by
    have hnat : (2692736703 : ℕ)^4183*100000000000000^3159 ≤ 44065555021211^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692736703 5000000000 44065555021211 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-445288589/2000000000 : ℝ), (2608653227/5000000000 : ℝ), (2692736703/5000000000 : ℝ)] ![(13681627585093/100000000000000 : ℝ), (21126408688523/50000000000000 : ℝ), (44065555021211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-445288589/2000000000 : ℝ)|^4183 ≤ (13681627585093/100000000000000 : ℝ)^3159
        have hw : |(-445288589/2000000000 : ℝ)|=(445288589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608653227/5000000000 : ℝ)|^4183 ≤ (21126408688523/50000000000000 : ℝ)^3159
        have hw : |(2608653227/5000000000 : ℝ)|=(2608653227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692736703/5000000000 : ℝ)|^4183 ≤ (44065555021211/100000000000000 : ℝ)^3159
        have hw : |(2692736703/5000000000 : ℝ)|=(2692736703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_9 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289474307/10000000000 : ℝ)*x 0 + (-213044343/1000000000 : ℝ)*x 1 + (1077094571/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289474307/10000000000 : ℝ)^4183 ≤ (43028458627747/100000000000000 : ℝ)^3159 := by
    have hnat : (5289474307 : ℕ)^4183*100000000000000^3159 ≤ 43028458627747^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289474307 10000000000 43028458627747 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (213044343/1000000000 : ℝ)^4183 ≤ (3226498076399/25000000000000 : ℝ)^3159 := by
    have hnat : (213044343 : ℕ)^4183*25000000000000^3159 ≤ 3226498076399^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213044343 1000000000 3226498076399 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077094571/2000000000 : ℝ)^4183 ≤ (44065549051337/100000000000000 : ℝ)^3159 := by
    have hnat : (1077094571 : ℕ)^4183*100000000000000^3159 ≤ 44065549051337^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077094571 2000000000 44065549051337 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289474307/10000000000 : ℝ), (-213044343/1000000000 : ℝ), (1077094571/2000000000 : ℝ)] ![(43028458627747/100000000000000 : ℝ), (3226498076399/25000000000000 : ℝ), (44065549051337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289474307/10000000000 : ℝ)|^4183 ≤ (43028458627747/100000000000000 : ℝ)^3159
        have hw : |(5289474307/10000000000 : ℝ)|=(5289474307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-213044343/1000000000 : ℝ)|^4183 ≤ (3226498076399/25000000000000 : ℝ)^3159
        have hw : |(-213044343/1000000000 : ℝ)|=(213044343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077094571/2000000000 : ℝ)|^4183 ≤ (44065549051337/100000000000000 : ℝ)^3159
        have hw : |(1077094571/2000000000 : ℝ)|=(1077094571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_10 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528947407/1000000000 : ℝ)*x 0 + (2692736249/5000000000 : ℝ)*x 1 + (-2130444231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528947407/1000000000 : ℝ)^4183 ≤ (43028456074871/100000000000000 : ℝ)^3159 := by
    have hnat : (528947407 : ℕ)^4183*100000000000000^3159 ≤ 43028456074871^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528947407 1000000000 43028456074871 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692736249/5000000000 : ℝ)^4183 ≤ (22032772591689/50000000000000 : ℝ)^3159 := by
    have hnat : (2692736249 : ℕ)^4183*50000000000000^3159 ≤ 22032772591689^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692736249 5000000000 22032772591689 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2130444231/10000000000 : ℝ)^4183 ≤ (6452999365439/50000000000000 : ℝ)^3159 := by
    have hnat : (2130444231 : ℕ)^4183*50000000000000^3159 ≤ 6452999365439^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130444231 10000000000 6452999365439 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528947407/1000000000 : ℝ), (2692736249/5000000000 : ℝ), (-2130444231/10000000000 : ℝ)] ![(43028456074871/100000000000000 : ℝ), (22032772591689/50000000000000 : ℝ), (6452999365439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528947407/1000000000 : ℝ)|^4183 ≤ (43028456074871/100000000000000 : ℝ)^3159
        have hw : |(528947407/1000000000 : ℝ)|=(528947407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692736249/5000000000 : ℝ)|^4183 ≤ (22032772591689/50000000000000 : ℝ)^3159
        have hw : |(2692736249/5000000000 : ℝ)|=(2692736249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2130444231/10000000000 : ℝ)|^4183 ≤ (6452999365439/50000000000000 : ℝ)^3159
        have hw : |(-2130444231/10000000000 : ℝ)|=(2130444231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_11 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4489152687/10000000000 : ℝ)*x 0 + (4297859587/10000000000 : ℝ)*x 1 + (2148929827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489152687/10000000000 : ℝ)^4183 ≤ (17313399352261/50000000000000 : ℝ)^3159 := by
    have hnat : (4489152687 : ℕ)^4183*50000000000000^3159 ≤ 17313399352261^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489152687 10000000000 17313399352261 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4297859587/10000000000 : ℝ)^4183 ≤ (8171650075583/25000000000000 : ℝ)^3159 := by
    have hnat : (4297859587 : ℕ)^4183*25000000000000^3159 ≤ 8171650075583^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297859587 10000000000 8171650075583 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148929827/5000000000 : ℝ)^4183 ≤ (32686600977063/100000000000000 : ℝ)^3159 := by
    have hnat : (2148929827 : ℕ)^4183*100000000000000^3159 ≤ 32686600977063^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148929827 5000000000 32686600977063 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489152687/10000000000 : ℝ), (4297859587/10000000000 : ℝ), (2148929827/5000000000 : ℝ)] ![(17313399352261/50000000000000 : ℝ), (8171650075583/25000000000000 : ℝ), (32686600977063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489152687/10000000000 : ℝ)|^4183 ≤ (17313399352261/50000000000000 : ℝ)^3159
        have hw : |(4489152687/10000000000 : ℝ)|=(4489152687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4297859587/10000000000 : ℝ)|^4183 ≤ (8171650075583/25000000000000 : ℝ)^3159
        have hw : |(4297859587/10000000000 : ℝ)|=(4297859587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2148929827/5000000000 : ℝ)|^4183 ≤ (32686600977063/100000000000000 : ℝ)^3159
        have hw : |(2148929827/5000000000 : ℝ)|=(2148929827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_12 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-259943119/1250000000 : ℝ)*x 0 + (1087764989/2000000000 : ℝ)*x 1 + (5273472671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259943119/1250000000 : ℝ)^4183 ≤ (312482397781/2500000000000 : ℝ)^3159 := by
    have hnat : (259943119 : ℕ)^4183*2500000000000^3159 ≤ 312482397781^3159*1250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259943119 1250000000 312482397781 2500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087764989/2000000000 : ℝ)^4183 ≤ (22322262307253/50000000000000 : ℝ)^3159 := by
    have hnat : (1087764989 : ℕ)^4183*50000000000000^3159 ≤ 22322262307253^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087764989 2000000000 22322262307253 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273472671/10000000000 : ℝ)^4183 ≤ (21428089729921/50000000000000 : ℝ)^3159 := by
    have hnat : (5273472671 : ℕ)^4183*50000000000000^3159 ≤ 21428089729921^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273472671 10000000000 21428089729921 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259943119/1250000000 : ℝ), (1087764989/2000000000 : ℝ), (5273472671/10000000000 : ℝ)] ![(312482397781/2500000000000 : ℝ), (22322262307253/50000000000000 : ℝ), (21428089729921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259943119/1250000000 : ℝ)|^4183 ≤ (312482397781/2500000000000 : ℝ)^3159
        have hw : |(-259943119/1250000000 : ℝ)|=(259943119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087764989/2000000000 : ℝ)|^4183 ≤ (22322262307253/50000000000000 : ℝ)^3159
        have hw : |(1087764989/2000000000 : ℝ)|=(1087764989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273472671/10000000000 : ℝ)|^4183 ≤ (21428089729921/50000000000000 : ℝ)^3159
        have hw : |(5273472671/10000000000 : ℝ)|=(5273472671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_13 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368548433/10000000000 : ℝ)*x 0 + (-1087310461/5000000000 : ℝ)*x 1 + (2636736187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368548433/10000000000 : ℝ)^4183 ≤ (43882272877061/100000000000000 : ℝ)^3159 := by
    have hnat : (5368548433 : ℕ)^4183*100000000000000^3159 ≤ 43882272877061^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368548433 10000000000 43882272877061 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087310461/5000000000 : ℝ)^4183 ≤ (6630775421943/50000000000000 : ℝ)^3159 := by
    have hnat : (1087310461 : ℕ)^4183*50000000000000^3159 ≤ 6630775421943^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087310461 5000000000 6630775421943 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636736187/5000000000 : ℝ)^4183 ≤ (334813877061/781250000000 : ℝ)^3159 := by
    have hnat : (2636736187 : ℕ)^4183*781250000000^3159 ≤ 334813877061^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636736187 5000000000 334813877061 781250000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368548433/10000000000 : ℝ), (-1087310461/5000000000 : ℝ), (2636736187/5000000000 : ℝ)] ![(43882272877061/100000000000000 : ℝ), (6630775421943/50000000000000 : ℝ), (334813877061/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368548433/10000000000 : ℝ)|^4183 ≤ (43882272877061/100000000000000 : ℝ)^3159
        have hw : |(5368548433/10000000000 : ℝ)|=(5368548433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087310461/5000000000 : ℝ)|^4183 ≤ (6630775421943/50000000000000 : ℝ)^3159
        have hw : |(-1087310461/5000000000 : ℝ)|=(1087310461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636736187/5000000000 : ℝ)|^4183 ≤ (334813877061/781250000000 : ℝ)^3159
        have hw : |(2636736187/5000000000 : ℝ)|=(2636736187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_14 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684274319/5000000000 : ℝ)*x 0 + (2636736327/5000000000 : ℝ)*x 1 + (-1087310137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684274319/5000000000 : ℝ)^4183 ≤ (10970568773973/25000000000000 : ℝ)^3159 := by
    have hnat : (2684274319 : ℕ)^4183*25000000000000^3159 ≤ 10970568773973^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684274319 5000000000 10970568773973 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636736327/5000000000 : ℝ)^4183 ≤ (5357022409613/12500000000000 : ℝ)^3159 := by
    have hnat : (2636736327 : ℕ)^4183*12500000000000^3159 ≤ 5357022409613^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636736327 5000000000 5357022409613 12500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087310137/5000000000 : ℝ)^4183 ≤ (1657693201401/12500000000000 : ℝ)^3159 := by
    have hnat : (1087310137 : ℕ)^4183*12500000000000^3159 ≤ 1657693201401^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087310137 5000000000 1657693201401 12500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684274319/5000000000 : ℝ), (2636736327/5000000000 : ℝ), (-1087310137/5000000000 : ℝ)] ![(10970568773973/25000000000000 : ℝ), (5357022409613/12500000000000 : ℝ), (1657693201401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684274319/5000000000 : ℝ)|^4183 ≤ (10970568773973/25000000000000 : ℝ)^3159
        have hw : |(2684274319/5000000000 : ℝ)|=(2684274319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636736327/5000000000 : ℝ)|^4183 ≤ (5357022409613/12500000000000 : ℝ)^3159
        have hw : |(2636736327/5000000000 : ℝ)|=(2636736327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087310137/5000000000 : ℝ)|^4183 ≤ (1657693201401/12500000000000 : ℝ)^3159
        have hw : |(-1087310137/5000000000 : ℝ)|=(1087310137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_box_15 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058542647/2500000000 : ℝ)*x 0 + (110633707/250000000 : ℝ)*x 1 + (4425348187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058542647/2500000000 : ℝ)^4183 ≤ (16023379444413/50000000000000 : ℝ)^3159 := by
    have hnat : (1058542647 : ℕ)^4183*50000000000000^3159 ≤ 16023379444413^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058542647 2500000000 16023379444413 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110633707/250000000 : ℝ)^4183 ≤ (169883105121/500000000000 : ℝ)^3159 := by
    have hnat : (110633707 : ℕ)^4183*500000000000^3159 ≤ 169883105121^3159*250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110633707 250000000 169883105121 500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4425348187/10000000000 : ℝ)^4183 ≤ (33976620078717/100000000000000 : ℝ)^3159 := by
    have hnat : (4425348187 : ℕ)^4183*100000000000000^3159 ≤ 33976620078717^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4425348187 10000000000 33976620078717 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058542647/2500000000 : ℝ), (110633707/250000000 : ℝ), (4425348187/10000000000 : ℝ)] ![(16023379444413/50000000000000 : ℝ), (169883105121/500000000000 : ℝ), (33976620078717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058542647/2500000000 : ℝ)|^4183 ≤ (16023379444413/50000000000000 : ℝ)^3159
        have hw : |(1058542647/2500000000 : ℝ)|=(1058542647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110633707/250000000 : ℝ)|^4183 ≤ (169883105121/500000000000 : ℝ)^3159
        have hw : |(110633707/250000000 : ℝ)|=(110633707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4425348187/10000000000 : ℝ)|^4183 ≤ (33976620078717/100000000000000 : ℝ)^3159
        have hw : |(4425348187/10000000000 : ℝ)|=(4425348187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1173_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12447/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59323/100000 : ℝ) ∧ (79903/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41597/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5697/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5697/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5697/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5697/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5697/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5697/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5697/50000 : ℝ) ^ (8365/2048 : ℝ) ≤ (14028776447418589/100000000000000000000 : ℝ) := by
    have hpowers : (5697/50000 : ℝ)^8365 ≤ (14028776447418589/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5697 : ℕ)^8365*100000000000000000000^2048 ≤ 14028776447418589^2048*50000^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5697 50000 14028776447418589 100000000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5697/50000 : ℝ)) (X := (14028776447418589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7033/50000 : ℝ) ^ (8365/2048 : ℝ) ≤ (3316852518289231/10000000000000000000 : ℝ) := by
    have hpowers : (7033/50000 : ℝ)^8365 ≤ (3316852518289231/10000000000000000000 : ℝ)^2048 := by
      have hnat : (7033 : ℕ)^8365*10000000000000000000^2048 ≤ 3316852518289231^2048*50000^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7033 50000 3316852518289231 10000000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7033/50000 : ℝ)) (X := (3316852518289231/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014028776447418589/50000000000000000000 : ℝ) ≤ (1000068685931561/1000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (50014028776447418589/50000000000000000000 : ℝ)^2048 ≤ (1000068685931561/1000000000000000 : ℝ)^8365 := by
      have hnat : (50014028776447418589 : ℕ)^2048*1000000000000000^8365 ≤ 1000068685931561^8365*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014028776447418589 50000000000000000000 1000068685931561 1000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000068685931561/1000000000000000 : ℝ)) (X := (50014028776447418589/50000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047197301630310899/100000000000000000000 : ℝ) ≤ (2000231064800241/2000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (100047197301630310899/100000000000000000000 : ℝ)^2048 ≤ (2000231064800241/2000000000000000 : ℝ)^8365 := by
      have hnat : (100047197301630310899 : ℕ)^2048*2000000000000000^8365 ≤ 2000231064800241^8365*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047197301630310899 100000000000000000000 2000231064800241 2000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000231064800241/2000000000000000 : ℝ)) (X := (100047197301630310899/100000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003316852518289231/5000000000000000000 : ℝ) ≤ (25004059471717/25000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (5003316852518289231/5000000000000000000 : ℝ)^2048 ≤ (25004059471717/25000000000000 : ℝ)^8365 := by
      have hnat : (5003316852518289231 : ℕ)^2048*25000000000000^8365 ≤ 25004059471717^8365*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003316852518289231 5000000000000000000 25004059471717 25000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25004059471717/25000000000000 : ℝ)) (X := (5003316852518289231/5000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14028776447418589/100000000000000000000 : ℝ) ≤ ((1335557995741798553/1336000000000000000 : ℝ)+2*(93692937119/53440000000000 : ℝ)*(5697/50000 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (1335557995741798553/1336000000000000000 : ℝ)+2*(93692937119/53440000000000 : ℝ)*(5697/50000 : ℝ)=(1000068685931561/1000000000000000 : ℝ) by norm_num, show 1+2*(14028776447418589/100000000000000000000 : ℝ)=(50014028776447418589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3316852518289231/10000000000000000000 : ℝ)+(14028776447418589/100000000000000000000 : ℝ) ≤ ((1335557995741798553/1336000000000000000 : ℝ)+(93692937119/53440000000000 : ℝ)*((7033/50000 : ℝ)+(5697/50000 : ℝ)))^(8365/2048 : ℝ) := by
    rw [show (1335557995741798553/1336000000000000000 : ℝ)+(93692937119/53440000000000 : ℝ)*((7033/50000 : ℝ)+(5697/50000 : ℝ))=(2000231064800241/2000000000000000 : ℝ) by norm_num, show 1+(3316852518289231/10000000000000000000 : ℝ)+(14028776447418589/100000000000000000000 : ℝ)=(100047197301630310899/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3316852518289231/10000000000000000000 : ℝ) ≤ ((1335557995741798553/1336000000000000000 : ℝ)+2*(93692937119/53440000000000 : ℝ)*(7033/50000 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (1335557995741798553/1336000000000000000 : ℝ)+2*(93692937119/53440000000000 : ℝ)*(7033/50000 : ℝ)=(25004059471717/25000000000000 : ℝ) by norm_num, show 1+2*(3316852518289231/10000000000000000000 : ℝ)=(5003316852518289231/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1335557995741798553/1336000000000000000 : ℝ)*(X 1 0+X 2 0)+(93692937119/53440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (5697/50000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (1335557995741798553/1336000000000000000 : ℝ)) (alpha := (93692937119/53440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1335557995741798553/1336000000000000000 : ℝ)*(X 0 1+X 2 1)+(93692937119/53440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (5697/50000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (1335557995741798553/1336000000000000000 : ℝ)) (alpha := (93692937119/53440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1335557995741798553/1336000000000000000 : ℝ)*(X 0 2+X 1 2)+(93692937119/53440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (5697/50000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (1335557995741798553/1336000000000000000 : ℝ)) (alpha := (93692937119/53440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-101313733/500000000 : ℝ)*X 0 0+(2687931187/5000000000 : ℝ)*X 0 1+(2687931291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296262269/10000000000 : ℝ)*X 1 0+(-1067150841/5000000000 : ℝ)*X 1 1+(167995713/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296261901/10000000000 : ℝ)*X 2 0+(5375862981/10000000000 : ℝ)*X 2 1+(-2134301953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4467542591/10000000000 : ℝ)*X 0 0+(430880527/1000000000 : ℝ)*X 0 1+(34470441/80000000 : ℝ)*X 0 2+(4467542591/10000000000 : ℝ)*X 1 0+(430880527/1000000000 : ℝ)*X 1 1+(34470441/80000000 : ℝ)*X 1 2+(4467542591/10000000000 : ℝ)*X 2 0+(430880527/1000000000 : ℝ)*X 2 1+(34470441/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-455882609/2000000000 : ℝ)*X 0 0+(5281524263/10000000000 : ℝ)*X 0 1+(1320381351/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681432849/5000000000 : ℝ)*X 1 0+(-434300477/2000000000 : ℝ)*X 1 1+(5281524759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681432869/5000000000 : ℝ)*X 2 0+(330095289/625000000 : ℝ)*X 2 1+(-2171502513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((531592037/1250000000 : ℝ)*X 0 0+(4416187981/10000000000 : ℝ)*X 0 1+(4416187511/10000000000 : ℝ)*X 0 2+(531592037/1250000000 : ℝ)*X 1 0+(4416187981/10000000000 : ℝ)*X 1 1+(4416187511/10000000000 : ℝ)*X 1 2+(531592037/1250000000 : ℝ)*X 2 0+(4416187981/10000000000 : ℝ)*X 2 1+(4416187511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-445288589/2000000000 : ℝ)*X 0 0+(2608653227/5000000000 : ℝ)*X 0 1+(2692736703/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289474307/10000000000 : ℝ)*X 1 0+(-213044343/1000000000 : ℝ)*X 1 1+(1077094571/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((528947407/1000000000 : ℝ)*X 2 0+(2692736249/5000000000 : ℝ)*X 2 1+(-2130444231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4489152687/10000000000 : ℝ)*X 0 0+(4297859587/10000000000 : ℝ)*X 0 1+(2148929827/5000000000 : ℝ)*X 0 2+(4489152687/10000000000 : ℝ)*X 1 0+(4297859587/10000000000 : ℝ)*X 1 1+(2148929827/5000000000 : ℝ)*X 1 2+(4489152687/10000000000 : ℝ)*X 2 0+(4297859587/10000000000 : ℝ)*X 2 1+(2148929827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-259943119/1250000000 : ℝ)*X 0 0+(1087764989/2000000000 : ℝ)*X 0 1+(5273472671/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368548433/10000000000 : ℝ)*X 1 0+(-1087310461/5000000000 : ℝ)*X 1 1+(2636736187/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684274319/5000000000 : ℝ)*X 2 0+(2636736327/5000000000 : ℝ)*X 2 1+(-1087310137/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1058542647/2500000000 : ℝ)*X 0 0+(110633707/250000000 : ℝ)*X 0 1+(4425348187/10000000000 : ℝ)*X 0 2+(1058542647/2500000000 : ℝ)*X 1 0+(110633707/250000000 : ℝ)*X 1 1+(4425348187/10000000000 : ℝ)*X 1 2+(1058542647/2500000000 : ℝ)*X 2 0+(110633707/250000000 : ℝ)*X 2 1+(4425348187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12447/20000 : ℝ) ≤ (-4157135376287389691544662946651/6680000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14078829/10000000000000 : ℝ)*(lower0) + (9451369/100000000000000 : ℝ)*(upper1) + (65307/125000000000 : ℝ)*(lower4) + (394642265417089/10000000000000 : ℝ)*(major0) + (394642265417089/10000000000000 : ℝ)*(major1) + (394642265417089/10000000000000 : ℝ)*(major2) + (32620499459/100000000000000 : ℝ)*(sp1) + (5454742239/12500000000000 : ℝ)*(sp2) + (2998742629/25000000000000 : ℝ)*(sp3) + (5283995127393039/100000000000000 : ℝ)*(sp4) + (1056798370878173/20000000000000 : ℝ)*(sp5) + (5283980836952411/100000000000000 : ℝ)*(sp6) + (32869412837317/1250000000000 : ℝ)*(sp7) + (7336874321/25000000000000 : ℝ)*(sp12) + (657391255488969/25000000000000 : ℝ)*(f.failure) + (5284024474890323/100000000000000 : ℝ)*(f.sum) + (3856933176093/1336000000000000000000000000 : ℝ)*base66 + (43545854143327217/13360000000000000000000000000000 : ℝ)*base67 + (4489368245647217/13360000000000000000000000000000 : ℝ)*base69 + (61824501127072783/13360000000000000000000000000000 : ℝ)*base72 + (17519460911843/1336000000000000000000000000 : ℝ)*base73 + (77743499334592783/13360000000000000000000000000000 : ℝ)*base76 + (77282173051887217/13360000000000000000000000000000 : ℝ)*base77 + (535793056836687217/13360000000000000000000000000000 : ℝ)*base79 + (261803738339/1336000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2397727/500000000000000000000 : ℝ)*base89 + (2397727/500000000000000000000 : ℝ)*base91 + (2397727/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59323/100000 : ℝ) ≤ (19814577724649468463285096576273/33400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (842049/625000000000 : ℝ)*(lower0) + (5686719/2500000000000 : ℝ)*(upper2) + (30957857/100000000000000 : ℝ)*(upper3) + (2005528008841747/50000000000000 : ℝ)*(major0) + (2005528008841747/50000000000000 : ℝ)*(major1) + (2005528008841747/50000000000000 : ℝ)*(major2) + (1065939460529979/20000000000000 : ℝ)*(sp0) + (666210830575061/12500000000000 : ℝ)*(sp1) + (2664845674744839/50000000000000 : ℝ)*(sp2) + (334077958712641/12500000000000 : ℝ)*(sp3) + (9544643999/50000000000000 : ℝ)*(sp5) + (1798049851/12500000000000 : ℝ)*(sp6) + (152082161/2000000000000 : ℝ)*(sp7) + (8431238591/100000000000000 : ℝ)*(sp12) + (2672631273809179/100000000000000 : ℝ)*(f.failure) + (2664852866944243/50000000000000 : ℝ)*(f.sum) + (66304359917/1336000000000000000000000000 : ℝ)*base65 + (388510716824917091/66800000000000000000000000000000 : ℝ)*base67 + (194487964263882909/66800000000000000000000000000000 : ℝ)*base70 + (45068743840282909/66800000000000000000000000000000 : ℝ)*base72 + (51385291366611/1336000000000000000000000000 : ℝ)*base74 + (290507703029082909/66800000000000000000000000000000 : ℝ)*base76 + (422135926681082909/66800000000000000000000000000000 : ℝ)*base78 + (2253095437146917091/66800000000000000000000000000000 : ℝ)*base79 + (12137629760461/1336000000000000000000000000 : ℝ)*base81 + (20272157/2000000000000000000000 : ℝ)*base89 + (20272157/2000000000000000000000 : ℝ)*base91 + (20272157/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79903/100000 : ℝ) ≤ (5337659354797546503079440980949/6680000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (466544731/100000000000000 : ℝ)*(upper0) + (245294081/100000000000000 : ℝ)*(upper1) + (55394629/25000000000000 : ℝ)*(upper2) + (315863997/50000000000000 : ℝ)*(lower5) + (447863298069311/10000000000000 : ℝ)*(major0) + (447863298069311/10000000000000 : ℝ)*(major1) + (447863298069311/10000000000000 : ℝ)*(major2) + (11880996781/10000000000000 : ℝ)*(sp1) + (1436270223/3125000000000 : ℝ)*(sp3) + (18906752403/100000000000000 : ℝ)*(sp4) + (2973213343679427/50000000000000 : ℝ)*(sp8) + (5946326784143447/100000000000000 : ℝ)*(sp9) + (743305699263907/12500000000000 : ℝ)*(sp10) + (373017422488409/12500000000000 : ℝ)*(sp11) + (373023167569301/12500000000000 : ℝ)*(f.failure) + (743305699263907/12500000000000 : ℝ)*(f.sum) + (71824259431/267200000000000000000000000 : ℝ)*base66 + (44497323780308017/13360000000000000000000000000000 : ℝ)*base68 + (33021582575908017/13360000000000000000000000000000 : ℝ)*base70 + (6738740212491983/13360000000000000000000000000000 : ℝ)*base71 + (13049700700299/1336000000000000000000000000 : ℝ)*base74 + (33053668072148017/13360000000000000000000000000000 : ℝ)*base76 + (22528407928868017/13360000000000000000000000000000 : ℝ)*base78 + (626522840718811983/13360000000000000000000000000000 : ℝ)*base79 + (1466778425627/1336000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1277683/250000000000000000000 : ℝ)*base89 + (1277683/250000000000000000000 : ℝ)*base91 + (1277683/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41597/50000 : ℝ) ≤ (-55571674734837295760153373249663/66800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100904217/100000000000000 : ℝ)*(lower1) + (188534043/50000000000000 : ℝ)*(lower2) + (124110713/100000000000000 : ℝ)*(upper5) + (4513790216797681/100000000000000 : ℝ)*(major0) + (4513790216797681/100000000000000 : ℝ)*(major1) + (4513790216797681/100000000000000 : ℝ)*(major2) + (910914847/5000000000000 : ℝ)*(sp0) + (580024274501/100000000000000 : ℝ)*(sp5) + (134653402017/100000000000000 : ℝ)*(sp6) + (55967520723/50000000000000 : ℝ)*(sp7) + (6047681418285927/100000000000000 : ℝ)*(sp12) + (3023559806154183/50000000000000 : ℝ)*(sp13) + (120951299663617/2000000000000 : ℝ)*(sp14) + (3007499238585231/100000000000000 : ℝ)*(sp15) + (751902793406669/25000000000000 : ℝ)*(f.failure) + (6047699636582867/100000000000000 : ℝ)*(f.sum) + (19374262506641/2672000000000000000000000000 : ℝ)*base66 + (1862358441956069407/133600000000000000000000000000000 : ℝ)*base68 + (719010900334469407/133600000000000000000000000000000 : ℝ)*base70 + (1661379852286469407/133600000000000000000000000000000 : ℝ)*base72 + (36285393068929/2672000000000000000000000000 : ℝ)*base74 + (1160485560080069407/133600000000000000000000000000000 : ℝ)*base76 + (690577946598469407/133600000000000000000000000000000 : ℝ)*base78 + (1001020261804869407/133600000000000000000000000000000 : ℝ)*base80 + (2043574077373/534400000000000000000000000 : ℝ)*base82 + (2456827/500000000000000000000 : ℝ)*base89 + (2456827/500000000000000000000 : ℝ)*base91 + (2456827/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1173_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59323/100000 : ℝ) else (79903/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41597/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1173_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1173_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59323/100000 : ℝ) else (79903/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41597/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1173_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59323/100000 : ℝ) else (79903/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41597/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1173_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
