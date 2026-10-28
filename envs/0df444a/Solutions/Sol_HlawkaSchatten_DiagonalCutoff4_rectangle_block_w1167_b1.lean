-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1167_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:43:10.474983+00:00
-- url     : https://prove2.me/submissions/a2891fef-e31b-4b3c-91ba-e24e32766dfe

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
theorem support_rectangle_w1167_s3_0 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151451287/10000000000 : ℝ)*x 0 + (5426649279/10000000000 : ℝ)*x 1 + (5234381769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151451287/10000000000 : ℝ)^1045 ≤ (13068588670451/100000000000000 : ℝ)^789 := by
    have hnat : (2151451287 : ℕ)^1045*100000000000000^789 ≤ 13068588670451^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151451287 10000000000 13068588670451 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426649279/10000000000 : ℝ)^1045 ≤ (11125962179899/25000000000000 : ℝ)^789 := by
    have hnat : (5426649279 : ℕ)^1045*25000000000000^789 ≤ 11125962179899^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426649279 10000000000 11125962179899 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234381769/10000000000 : ℝ)^1045 ≤ (10606890650461/25000000000000 : ℝ)^789 := by
    have hnat : (5234381769 : ℕ)^1045*25000000000000^789 ≤ 10606890650461^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234381769 10000000000 10606890650461 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151451287/10000000000 : ℝ), (5426649279/10000000000 : ℝ), (5234381769/10000000000 : ℝ)] ![(13068588670451/100000000000000 : ℝ), (11125962179899/25000000000000 : ℝ), (10606890650461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151451287/10000000000 : ℝ)|^1045 ≤ (13068588670451/100000000000000 : ℝ)^789
        have hw : |(-2151451287/10000000000 : ℝ)|=(2151451287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426649279/10000000000 : ℝ)|^1045 ≤ (11125962179899/25000000000000 : ℝ)^789
        have hw : |(5426649279/10000000000 : ℝ)|=(5426649279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234381769/10000000000 : ℝ)|^1045 ≤ (10606890650461/25000000000000 : ℝ)^789
        have hw : |(5234381769/10000000000 : ℝ)|=(5234381769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s3_1 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2676599357/5000000000 : ℝ)*x 0 + (-562419783/2500000000 : ℝ)*x 1 + (5234381573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676599357/5000000000 : ℝ)^1045 ≤ (21853897262889/50000000000000 : ℝ)^789 := by
    have hnat : (2676599357 : ℕ)^1045*50000000000000^789 ≤ 21853897262889^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676599357 5000000000 21853897262889 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562419783/2500000000 : ℝ)^1045 ≤ (554585798303/4000000000000 : ℝ)^789 := by
    have hnat : (562419783 : ℕ)^1045*4000000000000^789 ≤ 554585798303^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562419783 2500000000 554585798303 4000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234381573/10000000000 : ℝ)^1045 ≤ (42427560497687/100000000000000 : ℝ)^789 := by
    have hnat : (5234381573 : ℕ)^1045*100000000000000^789 ≤ 42427560497687^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234381573 10000000000 42427560497687 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676599357/5000000000 : ℝ), (-562419783/2500000000 : ℝ), (5234381573/10000000000 : ℝ)] ![(21853897262889/50000000000000 : ℝ), (554585798303/4000000000000 : ℝ), (42427560497687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676599357/5000000000 : ℝ)|^1045 ≤ (21853897262889/50000000000000 : ℝ)^789
        have hw : |(2676599357/5000000000 : ℝ)|=(2676599357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-562419783/2500000000 : ℝ)|^1045 ≤ (554585798303/4000000000000 : ℝ)^789
        have hw : |(-562419783/2500000000 : ℝ)|=(562419783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234381573/10000000000 : ℝ)|^1045 ≤ (42427560497687/100000000000000 : ℝ)^789
        have hw : |(5234381573/10000000000 : ℝ)|=(5234381573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s3_2 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5353198797/10000000000 : ℝ)*x 0 + (2617190791/5000000000 : ℝ)*x 1 + (-2249679011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353198797/10000000000 : ℝ)^1045 ≤ (43707795423337/100000000000000 : ℝ)^789 := by
    have hnat : (5353198797 : ℕ)^1045*100000000000000^789 ≤ 43707795423337^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353198797 10000000000 43707795423337 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617190791/5000000000 : ℝ)^1045 ≤ (21213780297153/50000000000000 : ℝ)^789 := by
    have hnat : (2617190791 : ℕ)^1045*50000000000000^789 ≤ 21213780297153^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617190791 5000000000 21213780297153 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249679011/10000000000 : ℝ)^1045 ≤ (13864643969903/100000000000000 : ℝ)^789 := by
    have hnat : (2249679011 : ℕ)^1045*100000000000000^789 ≤ 13864643969903^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249679011 10000000000 13864643969903 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353198797/10000000000 : ℝ), (2617190791/5000000000 : ℝ), (-2249679011/10000000000 : ℝ)] ![(43707795423337/100000000000000 : ℝ), (21213780297153/50000000000000 : ℝ), (13864643969903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353198797/10000000000 : ℝ)|^1045 ≤ (43707795423337/100000000000000 : ℝ)^789
        have hw : |(5353198797/10000000000 : ℝ)|=(5353198797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617190791/5000000000 : ℝ)|^1045 ≤ (21213780297153/50000000000000 : ℝ)^789
        have hw : |(2617190791/5000000000 : ℝ)|=(2617190791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2249679011/10000000000 : ℝ)|^1045 ≤ (13864643969903/100000000000000 : ℝ)^789
        have hw : |(-2249679011/10000000000 : ℝ)|=(2249679011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s3_3 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4359060423/10000000000 : ℝ)*x 0 + (2085526337/5000000000 : ℝ)*x 1 + (2277720253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359060423/10000000000 : ℝ)^1045 ≤ (33295828148513/100000000000000 : ℝ)^789 := by
    have hnat : (4359060423 : ℕ)^1045*100000000000000^789 ≤ 33295828148513^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359060423 10000000000 33295828148513 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085526337/5000000000 : ℝ)^1045 ≤ (7851815468047/25000000000000 : ℝ)^789 := by
    have hnat : (2085526337 : ℕ)^1045*25000000000000^789 ≤ 7851815468047^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085526337 5000000000 7851815468047 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2277720253/5000000000 : ℝ)^1045 ≤ (35296909968267/100000000000000 : ℝ)^789 := by
    have hnat : (2277720253 : ℕ)^1045*100000000000000^789 ≤ 35296909968267^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277720253 5000000000 35296909968267 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359060423/10000000000 : ℝ), (2085526337/5000000000 : ℝ), (2277720253/5000000000 : ℝ)] ![(33295828148513/100000000000000 : ℝ), (7851815468047/25000000000000 : ℝ), (35296909968267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359060423/10000000000 : ℝ)|^1045 ≤ (33295828148513/100000000000000 : ℝ)^789
        have hw : |(4359060423/10000000000 : ℝ)|=(4359060423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085526337/5000000000 : ℝ)|^1045 ≤ (7851815468047/25000000000000 : ℝ)^789
        have hw : |(2085526337/5000000000 : ℝ)|=(2085526337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2277720253/5000000000 : ℝ)|^1045 ≤ (35296909968267/100000000000000 : ℝ)^789
        have hw : |(2277720253/5000000000 : ℝ)|=(2277720253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s3_4 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151468129/10000000000 : ℝ)*x 0 + (163597339/312500000 : ℝ)*x 1 + (2712956111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151468129/10000000000 : ℝ)^1045 ≤ (13068724167761/100000000000000 : ℝ)^789 := by
    have hnat : (2151468129 : ℕ)^1045*100000000000000^789 ≤ 13068724167761^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151468129 10000000000 13068724167761 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163597339/312500000 : ℝ)^1045 ≤ (21217716372401/50000000000000 : ℝ)^789 := by
    have hnat : (163597339 : ℕ)^1045*50000000000000^789 ≤ 21217716372401^789*312500000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163597339 312500000 21217716372401 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712956111/5000000000 : ℝ)^1045 ≤ (22247921534709/50000000000000 : ℝ)^789 := by
    have hnat : (2712956111 : ℕ)^1045*50000000000000^789 ≤ 22247921534709^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712956111 5000000000 22247921534709 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151468129/10000000000 : ℝ), (163597339/312500000 : ℝ), (2712956111/5000000000 : ℝ)] ![(13068724167761/100000000000000 : ℝ), (21217716372401/50000000000000 : ℝ), (22247921534709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151468129/10000000000 : ℝ)|^1045 ≤ (13068724167761/100000000000000 : ℝ)^789
        have hw : |(-2151468129/10000000000 : ℝ)|=(2151468129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163597339/312500000 : ℝ)|^1045 ≤ (21217716372401/50000000000000 : ℝ)^789
        have hw : |(163597339/312500000 : ℝ)|=(163597339/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712956111/5000000000 : ℝ)|^1045 ≤ (22247921534709/50000000000000 : ℝ)^789
        have hw : |(2712956111/5000000000 : ℝ)|=(2712956111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s3_5 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5304400111/10000000000 : ℝ)*x 0 + (-2058149209/10000000000 : ℝ)*x 1 + (1356477999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304400111/10000000000 : ℝ)^1045 ≤ (43180870328127/100000000000000 : ℝ)^789 := by
    have hnat : (5304400111 : ℕ)^1045*100000000000000^789 ≤ 43180870328127^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304400111 10000000000 43180870328127 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058149209/10000000000 : ℝ)^1045 ≤ (6161644521791/50000000000000 : ℝ)^789 := by
    have hnat : (2058149209 : ℕ)^1045*50000000000000^789 ≤ 6161644521791^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058149209 10000000000 6161644521791 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356477999/2500000000 : ℝ)^1045 ≤ (44495840614741/100000000000000 : ℝ)^789 := by
    have hnat : (1356477999 : ℕ)^1045*100000000000000^789 ≤ 44495840614741^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356477999 2500000000 44495840614741 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304400111/10000000000 : ℝ), (-2058149209/10000000000 : ℝ), (1356477999/2500000000 : ℝ)] ![(43180870328127/100000000000000 : ℝ), (6161644521791/50000000000000 : ℝ), (44495840614741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304400111/10000000000 : ℝ)|^1045 ≤ (43180870328127/100000000000000 : ℝ)^789
        have hw : |(5304400111/10000000000 : ℝ)|=(5304400111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058149209/10000000000 : ℝ)|^1045 ≤ (6161644521791/50000000000000 : ℝ)^789
        have hw : |(-2058149209/10000000000 : ℝ)|=(2058149209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356477999/2500000000 : ℝ)|^1045 ≤ (44495840614741/100000000000000 : ℝ)^789
        have hw : |(1356477999/2500000000 : ℝ)|=(1356477999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s3_6 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (10360159/19531250 : ℝ)*x 0 + (339119429/625000000 : ℝ)*x 1 + (-514537249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10360159/19531250 : ℝ)^1045 ≤ (43180884312223/100000000000000 : ℝ)^789 := by
    have hnat : (10360159 : ℕ)^1045*100000000000000^789 ≤ 43180884312223^789*19531250^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10360159 19531250 43180884312223 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339119429/625000000 : ℝ)^1045 ≤ (2780989269977/6250000000000 : ℝ)^789 := by
    have hnat : (339119429 : ℕ)^1045*6250000000000^789 ≤ 2780989269977^789*625000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339119429 625000000 2780989269977 6250000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514537249/2500000000 : ℝ)^1045 ≤ (12323287354431/100000000000000 : ℝ)^789 := by
    have hnat : (514537249 : ℕ)^1045*100000000000000^789 ≤ 12323287354431^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514537249 2500000000 12323287354431 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10360159/19531250 : ℝ), (339119429/625000000 : ℝ), (-514537249/2500000000 : ℝ)] ![(43180884312223/100000000000000 : ℝ), (2780989269977/6250000000000 : ℝ), (12323287354431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10360159/19531250 : ℝ)|^1045 ≤ (43180884312223/100000000000000 : ℝ)^789
        have hw : |(10360159/19531250 : ℝ)|=(10360159/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339119429/625000000 : ℝ)|^1045 ≤ (2780989269977/6250000000000 : ℝ)^789
        have hw : |(339119429/625000000 : ℝ)|=(339119429/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-514537249/2500000000 : ℝ)|^1045 ≤ (12323287354431/100000000000000 : ℝ)^789
        have hw : |(-514537249/2500000000 : ℝ)|=(514537249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s3_7 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (871818759/2000000000 : ℝ)*x 0 + (910795031/2000000000 : ℝ)*x 1 + (2086263263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871818759/2000000000 : ℝ)^1045 ≤ (33296165761383/100000000000000 : ℝ)^789 := by
    have hnat : (871818759 : ℕ)^1045*100000000000000^789 ≤ 33296165761383^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871818759 2000000000 33296165761383 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910795031/2000000000 : ℝ)^1045 ≤ (1411274914029/4000000000000 : ℝ)^789 := by
    have hnat : (910795031 : ℕ)^1045*4000000000000^789 ≤ 1411274914029^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910795031 2000000000 1411274914029 4000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086263263/5000000000 : ℝ)^1045 ≤ (6284392273721/20000000000000 : ℝ)^789 := by
    have hnat : (2086263263 : ℕ)^1045*20000000000000^789 ≤ 6284392273721^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086263263 5000000000 6284392273721 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871818759/2000000000 : ℝ), (910795031/2000000000 : ℝ), (2086263263/5000000000 : ℝ)] ![(33296165761383/100000000000000 : ℝ), (1411274914029/4000000000000 : ℝ), (6284392273721/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871818759/2000000000 : ℝ)|^1045 ≤ (33296165761383/100000000000000 : ℝ)^789
        have hw : |(871818759/2000000000 : ℝ)|=(871818759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(910795031/2000000000 : ℝ)|^1045 ≤ (1411274914029/4000000000000 : ℝ)^789
        have hw : |(910795031/2000000000 : ℝ)|=(910795031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086263263/5000000000 : ℝ)|^1045 ≤ (6284392273721/20000000000000 : ℝ)^789
        have hw : |(2086263263/5000000000 : ℝ)|=(2086263263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1167_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16429/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2677/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14777/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16429/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16429/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16429/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16429/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16429/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16429/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4591/50000 : ℝ) ^ (8359/2048 : ℝ) ≤ (2925189364781607/50000000000000000000 : ℝ) := by
    have hpowers : (4591/50000 : ℝ)^8359 ≤ (2925189364781607/50000000000000000000 : ℝ)^2048 := by
      have hnat : (4591 : ℕ)^8359*50000000000000000000^2048 ≤ 2925189364781607^2048*50000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4591 50000 2925189364781607 50000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4591/50000 : ℝ)) (X := (2925189364781607/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16429/100000 : ℝ) ^ (8359/2048 : ℝ) ≤ (15718935430467221/25000000000000000000 : ℝ) := by
    have hpowers : (16429/100000 : ℝ)^8359 ≤ (15718935430467221/25000000000000000000 : ℝ)^2048 := by
      have hnat : (16429 : ℕ)^8359*25000000000000000000^2048 ≤ 15718935430467221^2048*100000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16429 100000 15718935430467221 25000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16429/100000 : ℝ)) (X := (15718935430467221/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002925189364781607/25000000000000000000 : ℝ) ≤ (10000286662195183/10000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (25002925189364781607/25000000000000000000 : ℝ)^2048 ≤ (10000286662195183/10000000000000000 : ℝ)^8359 := by
      have hnat : (25002925189364781607 : ℕ)^2048*10000000000000000^8359 ≤ 10000286662195183^8359*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002925189364781607 25000000000000000000 10000286662195183 10000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000286662195183/10000000000000000 : ℝ)) (X := (25002925189364781607/25000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50034363060225716049/50000000000000000000 : ℝ) ≤ (5000841695136977/5000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (50034363060225716049/50000000000000000000 : ℝ)^2048 ≤ (5000841695136977/5000000000000000 : ℝ)^8359 := by
      have hnat : (50034363060225716049 : ℕ)^2048*5000000000000000^8359 ≤ 5000841695136977^8359*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034363060225716049 50000000000000000000 5000841695136977 5000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000841695136977/5000000000000000 : ℝ)) (X := (50034363060225716049/50000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12515718935430467221/12500000000000000000 : ℝ) ≤ (400123204734109/400000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (12515718935430467221/12500000000000000000 : ℝ)^2048 ≤ (400123204734109/400000000000000 : ℝ)^8359 := by
      have hnat : (12515718935430467221 : ℕ)^2048*400000000000000^8359 ≤ 400123204734109^8359*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12515718935430467221 12500000000000000000 400123204734109 400000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400123204734109/400000000000000 : ℝ)) (X := (12515718935430467221/12500000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2925189364781607/50000000000000000000 : ℝ) ≤ ((72446427926489940557/72470000000000000000 : ℝ)+2*(1396728078771/724700000000000 : ℝ)*(4591/50000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (72446427926489940557/72470000000000000000 : ℝ)+2*(1396728078771/724700000000000 : ℝ)*(4591/50000 : ℝ)=(10000286662195183/10000000000000000 : ℝ) by norm_num, show 1+2*(2925189364781607/50000000000000000000 : ℝ)=(25002925189364781607/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15718935430467221/25000000000000000000 : ℝ)+(2925189364781607/50000000000000000000 : ℝ) ≤ ((72446427926489940557/72470000000000000000 : ℝ)+(1396728078771/724700000000000 : ℝ)*((16429/100000 : ℝ)+(4591/50000 : ℝ)))^(8359/2048 : ℝ) := by
    rw [show (72446427926489940557/72470000000000000000 : ℝ)+(1396728078771/724700000000000 : ℝ)*((16429/100000 : ℝ)+(4591/50000 : ℝ))=(5000841695136977/5000000000000000 : ℝ) by norm_num, show 1+(15718935430467221/25000000000000000000 : ℝ)+(2925189364781607/50000000000000000000 : ℝ)=(50034363060225716049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15718935430467221/25000000000000000000 : ℝ) ≤ ((72446427926489940557/72470000000000000000 : ℝ)+2*(1396728078771/724700000000000 : ℝ)*(16429/100000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (72446427926489940557/72470000000000000000 : ℝ)+2*(1396728078771/724700000000000 : ℝ)*(16429/100000 : ℝ)=(400123204734109/400000000000000 : ℝ) by norm_num, show 1+2*(15718935430467221/25000000000000000000 : ℝ)=(12515718935430467221/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72446427926489940557/72470000000000000000 : ℝ)*(X 1 0+X 2 0)+(1396728078771/724700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (4591/50000 : ℝ)) (hi := (16429/100000 : ℝ)) (c := (72446427926489940557/72470000000000000000 : ℝ)) (alpha := (1396728078771/724700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72446427926489940557/72470000000000000000 : ℝ)*(X 0 1+X 2 1)+(1396728078771/724700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (4591/50000 : ℝ)) (hi := (16429/100000 : ℝ)) (c := (72446427926489940557/72470000000000000000 : ℝ)) (alpha := (1396728078771/724700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72446427926489940557/72470000000000000000 : ℝ)*(X 0 2+X 1 2)+(1396728078771/724700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (4591/50000 : ℝ)) (hi := (16429/100000 : ℝ)) (c := (72446427926489940557/72470000000000000000 : ℝ)) (alpha := (1396728078771/724700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2151451287/10000000000 : ℝ)*X 0 0+(5426649279/10000000000 : ℝ)*X 0 1+(5234381769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676599357/5000000000 : ℝ)*X 1 0+(-562419783/2500000000 : ℝ)*X 1 1+(5234381573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353198797/10000000000 : ℝ)*X 2 0+(2617190791/5000000000 : ℝ)*X 2 1+(-2249679011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359060423/10000000000 : ℝ)*X 0 0+(2085526337/5000000000 : ℝ)*X 0 1+(2277720253/5000000000 : ℝ)*X 0 2+(4359060423/10000000000 : ℝ)*X 1 0+(2085526337/5000000000 : ℝ)*X 1 1+(2277720253/5000000000 : ℝ)*X 1 2+(4359060423/10000000000 : ℝ)*X 2 0+(2085526337/5000000000 : ℝ)*X 2 1+(2277720253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151468129/10000000000 : ℝ)*X 0 0+(163597339/312500000 : ℝ)*X 0 1+(2712956111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304400111/10000000000 : ℝ)*X 1 0+(-2058149209/10000000000 : ℝ)*X 1 1+(1356477999/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((10360159/19531250 : ℝ)*X 2 0+(339119429/625000000 : ℝ)*X 2 1+(-514537249/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871818759/2000000000 : ℝ)*X 0 0+(910795031/2000000000 : ℝ)*X 0 1+(2086263263/5000000000 : ℝ)*X 0 2+(871818759/2000000000 : ℝ)*X 1 0+(910795031/2000000000 : ℝ)*X 1 1+(2086263263/5000000000 : ℝ)*X 1 2+(871818759/2000000000 : ℝ)*X 2 0+(910795031/2000000000 : ℝ)*X 2 1+(2086263263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4281008300281877424860391513/905875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1232370431/100000000000000 : ℝ)*(base19) + (1201668201/100000000000000 : ℝ)*(base23) + (29802421/50000000000000 : ℝ)*(lower2) + (80213351/100000000000000 : ℝ)*(upper3) + (17737029/12500000000000 : ℝ)*(upper5) + (975335477978497/25000000000000 : ℝ)*(major0) + (975335477978497/25000000000000 : ℝ)*(major1) + (975335477978497/25000000000000 : ℝ)*(major2) + (2600552011134251/50000000000000 : ℝ)*(sp0) + (5201123942947867/100000000000000 : ℝ)*(sp1) + (5201123973650097/100000000000000 : ℝ)*(sp2) + (2601548865419473/100000000000000 : ℝ)*(sp3) + (5288262449/25000000000000 : ℝ)*(sp4) + (9625562637/100000000000000 : ℝ)*(sp7) + (2601558490982111/100000000000000 : ℝ)*(f.failure) + (2600562587659149/50000000000000 : ℝ)*(f.sum) + (27107314205053/9058750000000000000000000000 : ℝ)*base66 + (7676613070537652829/1811750000000000000000000000000000 : ℝ)*base67 + (3369098549260402829/1811750000000000000000000000000000 : ℝ)*base69 + (5326338291828097171/1811750000000000000000000000000000 : ℝ)*base72 + (37168323023893/36235000000000000000000000000 : ℝ)*base73 + (38260309005978652829/1811750000000000000000000000000000 : ℝ)*base75 + (19758539990312347171/1811750000000000000000000000000000 : ℝ)*base78 + (48977932091578652829/1811750000000000000000000000000000 : ℝ)*base79 + (123518510797507/36235000000000000000000000000 : ℝ)*base82 + (18377571/5000000000000000000000 : ℝ)*base89 + (18377571/5000000000000000000000 : ℝ)*base91 + (18377571/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8337965721129509884882172751/905875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1261723703/100000000000000 : ℝ)*(base19) + (1338272553/50000000000000 : ℝ)*(base23) + (119061317/100000000000000 : ℝ)*(upper3) + (13510997/100000000000000 : ℝ)*(lower4) + (7927763/6250000000000 : ℝ)*(upper5) + (982845174935173/25000000000000 : ℝ)*(major0) + (982845174935173/25000000000000 : ℝ)*(major1) + (982845174935173/25000000000000 : ℝ)*(major2) + (17731476949/100000000000000 : ℝ)*(sp1) + (14725624057/50000000000000 : ℝ)*(sp2) + (2620585815750433/50000000000000 : ℝ)*(sp4) + (2620576319150107/50000000000000 : ℝ)*(sp5) + (5241139503707647/100000000000000 : ℝ)*(sp6) + (2621589461169759/100000000000000 : ℝ)*(sp7) + (2621589461169759/100000000000000 : ℝ)*(f.failure) + (2620585815750433/50000000000000 : ℝ)*(f.sum) + (56411848436147/36235000000000000000000000000 : ℝ)*base65 + (2247067548784061361/1811750000000000000000000000000000 : ℝ)*base67 + (32274621665576311361/1811750000000000000000000000000000 : ℝ)*base69 + (23166589784583061361/1811750000000000000000000000000000 : ℝ)*base71 + (132254120369453/36235000000000000000000000000 : ℝ)*base74 + (4955526648265561361/1811750000000000000000000000000000 : ℝ)*base75 + (6353335103078561361/1811750000000000000000000000000000 : ℝ)*base77 + (7954886299275061361/1811750000000000000000000000000000 : ℝ)*base79 + (10631885750763/9058750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3017501/5000000000000000000000 : ℝ)*base90 + (3017501/5000000000000000000000 : ℝ)*base92 + (3017501/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1167_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16429/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1167_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1167_s4_0 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154256857/10000000000 : ℝ)*x 0 + (2700360981/5000000000 : ℝ)*x 1 + (657309133/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154256857/10000000000 : ℝ)^1045 ≤ (13091164795823/100000000000000 : ℝ)^789 := by
    have hnat : (2154256857 : ℕ)^1045*100000000000000^789 ≤ 13091164795823^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154256857 10000000000 13091164795823 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700360981/5000000000 : ℝ)^1045 ≤ (8844489553171/20000000000000 : ℝ)^789 := by
    have hnat : (2700360981 : ℕ)^1045*20000000000000^789 ≤ 8844489553171^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700360981 5000000000 8844489553171 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657309133/1250000000 : ℝ)^1045 ≤ (42686387432701/100000000000000 : ℝ)^789 := by
    have hnat : (657309133 : ℕ)^1045*100000000000000^789 ≤ 42686387432701^789*1250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657309133 1250000000 42686387432701 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154256857/10000000000 : ℝ), (2700360981/5000000000 : ℝ), (657309133/1250000000 : ℝ)] ![(13091164795823/100000000000000 : ℝ), (8844489553171/20000000000000 : ℝ), (42686387432701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154256857/10000000000 : ℝ)|^1045 ≤ (13091164795823/100000000000000 : ℝ)^789
        have hw : |(-2154256857/10000000000 : ℝ)|=(2154256857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700360981/5000000000 : ℝ)|^1045 ≤ (8844489553171/20000000000000 : ℝ)^789
        have hw : |(2700360981/5000000000 : ℝ)|=(2700360981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657309133/1250000000 : ℝ)|^1045 ≤ (42686387432701/100000000000000 : ℝ)^789
        have hw : |(657309133/1250000000 : ℝ)|=(657309133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s4_1 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673354273/5000000000 : ℝ)*x 0 + (-2226527843/10000000000 : ℝ)*x 1 + (5258473223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673354273/5000000000 : ℝ)^1045 ≤ (272735149423/625000000000 : ℝ)^789 := by
    have hnat : (2673354273 : ℕ)^1045*625000000000^789 ≤ 272735149423^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673354273 5000000000 272735149423 625000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2226527843/10000000000 : ℝ)^1045 ≤ (341899673313/2500000000000 : ℝ)^789 := by
    have hnat : (2226527843 : ℕ)^1045*2500000000000^789 ≤ 341899673313^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226527843 10000000000 341899673313 2500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258473223/10000000000 : ℝ)^1045 ≤ (42686389142189/100000000000000 : ℝ)^789 := by
    have hnat : (5258473223 : ℕ)^1045*100000000000000^789 ≤ 42686389142189^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258473223 10000000000 42686389142189 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673354273/5000000000 : ℝ), (-2226527843/10000000000 : ℝ), (5258473223/10000000000 : ℝ)] ![(272735149423/625000000000 : ℝ), (341899673313/2500000000000 : ℝ), (42686389142189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673354273/5000000000 : ℝ)|^1045 ≤ (272735149423/625000000000 : ℝ)^789
        have hw : |(2673354273/5000000000 : ℝ)|=(2673354273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2226527843/10000000000 : ℝ)|^1045 ≤ (341899673313/2500000000000 : ℝ)^789
        have hw : |(-2226527843/10000000000 : ℝ)|=(2226527843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258473223/10000000000 : ℝ)|^1045 ≤ (42686389142189/100000000000000 : ℝ)^789
        have hw : |(5258473223/10000000000 : ℝ)|=(5258473223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s4_2 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5346708387/10000000000 : ℝ)*x 0 + (2629236633/5000000000 : ℝ)*x 1 + (-1113263999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346708387/10000000000 : ℝ)^1045 ≤ (43637622188937/100000000000000 : ℝ)^789 := by
    have hnat : (5346708387 : ℕ)^1045*100000000000000^789 ≤ 43637622188937^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346708387 10000000000 43637622188937 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629236633/5000000000 : ℝ)^1045 ≤ (5335798700563/12500000000000 : ℝ)^789 := by
    have hnat : (2629236633 : ℕ)^1045*12500000000000^789 ≤ 5335798700563^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629236633 5000000000 5335798700563 12500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113263999/5000000000 : ℝ)^1045 ≤ (13675988193481/100000000000000 : ℝ)^789 := by
    have hnat : (1113263999 : ℕ)^1045*100000000000000^789 ≤ 13675988193481^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113263999 5000000000 13675988193481 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346708387/10000000000 : ℝ), (2629236633/5000000000 : ℝ), (-1113263999/5000000000 : ℝ)] ![(43637622188937/100000000000000 : ℝ), (5335798700563/12500000000000 : ℝ), (13675988193481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346708387/10000000000 : ℝ)|^1045 ≤ (43637622188937/100000000000000 : ℝ)^789
        have hw : |(5346708387/10000000000 : ℝ)|=(5346708387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629236633/5000000000 : ℝ)|^1045 ≤ (5335798700563/12500000000000 : ℝ)^789
        have hw : |(2629236633/5000000000 : ℝ)|=(2629236633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1113263999/5000000000 : ℝ)|^1045 ≤ (13675988193481/100000000000000 : ℝ)^789
        have hw : |(-1113263999/5000000000 : ℝ)|=(1113263999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s4_3 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (109018431/250000000 : ℝ)*x 0 + (2110417899/5000000000 : ℝ)*x 1 + (1126306141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109018431/250000000 : ℝ)^1045 ≤ (33312792958011/100000000000000 : ℝ)^789 := by
    have hnat : (109018431 : ℕ)^1045*100000000000000^789 ≤ 33312792958011^789*250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109018431 250000000 33312792958011 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110417899/5000000000 : ℝ)^1045 ≤ (31904705297551/100000000000000 : ℝ)^789 := by
    have hnat : (2110417899 : ℕ)^1045*100000000000000^789 ≤ 31904705297551^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110417899 5000000000 31904705297551 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126306141/2500000000 : ℝ)^1045 ≤ (34782501726557/100000000000000 : ℝ)^789 := by
    have hnat : (1126306141 : ℕ)^1045*100000000000000^789 ≤ 34782501726557^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126306141 2500000000 34782501726557 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109018431/250000000 : ℝ), (2110417899/5000000000 : ℝ), (1126306141/2500000000 : ℝ)] ![(33312792958011/100000000000000 : ℝ), (31904705297551/100000000000000 : ℝ), (34782501726557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109018431/250000000 : ℝ)|^1045 ≤ (33312792958011/100000000000000 : ℝ)^789
        have hw : |(109018431/250000000 : ℝ)|=(109018431/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110417899/5000000000 : ℝ)|^1045 ≤ (31904705297551/100000000000000 : ℝ)^789
        have hw : |(2110417899/5000000000 : ℝ)|=(2110417899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126306141/2500000000 : ℝ)|^1045 ≤ (34782501726557/100000000000000 : ℝ)^789
        have hw : |(1126306141/2500000000 : ℝ)|=(1126306141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s4_4 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-3366037/15625000 : ℝ)*x 0 + (2629437587/5000000000 : ℝ)*x 1 + (1080063649/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3366037/15625000 : ℝ)^1045 ≤ (13091219711417/100000000000000 : ℝ)^789 := by
    have hnat : (3366037 : ℕ)^1045*100000000000000^789 ≤ 13091219711417^789*15625000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3366037 15625000 13091219711417 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629437587/5000000000 : ℝ)^1045 ≤ (42690710771761/100000000000000 : ℝ)^789 := by
    have hnat : (2629437587 : ℕ)^1045*100000000000000^789 ≤ 42690710771761^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629437587 5000000000 42690710771761 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080063649/2000000000 : ℝ)^1045 ≤ (44218069501143/100000000000000 : ℝ)^789 := by
    have hnat : (1080063649 : ℕ)^1045*100000000000000^789 ≤ 44218069501143^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080063649 2000000000 44218069501143 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3366037/15625000 : ℝ), (2629437587/5000000000 : ℝ), (1080063649/2000000000 : ℝ)] ![(13091219711417/100000000000000 : ℝ), (42690710771761/100000000000000 : ℝ), (44218069501143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3366037/15625000 : ℝ)|^1045 ≤ (13091219711417/100000000000000 : ℝ)^789
        have hw : |(-3366037/15625000 : ℝ)|=(3366037/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629437587/5000000000 : ℝ)|^1045 ≤ (42690710771761/100000000000000 : ℝ)^789
        have hw : |(2629437587/5000000000 : ℝ)|=(2629437587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080063649/2000000000 : ℝ)|^1045 ≤ (44218069501143/100000000000000 : ℝ)^789
        have hw : |(1080063649/2000000000 : ℝ)|=(1080063649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s4_5 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1327651309/2500000000 : ℝ)*x 0 + (-1042341327/5000000000 : ℝ)*x 1 + (1080063627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327651309/2500000000 : ℝ)^1045 ≤ (2702986620043/6250000000000 : ℝ)^789 := by
    have hnat : (1327651309 : ℕ)^1045*6250000000000^789 ≤ 2702986620043^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327651309 2500000000 2702986620043 6250000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042341327/5000000000 : ℝ)^1045 ≤ (12534145765619/100000000000000 : ℝ)^789 := by
    have hnat : (1042341327 : ℕ)^1045*100000000000000^789 ≤ 12534145765619^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042341327 5000000000 12534145765619 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080063627/2000000000 : ℝ)^1045 ≤ (2210903415411/5000000000000 : ℝ)^789 := by
    have hnat : (1080063627 : ℕ)^1045*5000000000000^789 ≤ 2210903415411^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080063627 2000000000 2210903415411 5000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327651309/2500000000 : ℝ), (-1042341327/5000000000 : ℝ), (1080063627/2000000000 : ℝ)] ![(2702986620043/6250000000000 : ℝ), (12534145765619/100000000000000 : ℝ), (2210903415411/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327651309/2500000000 : ℝ)|^1045 ≤ (2702986620043/6250000000000 : ℝ)^789
        have hw : |(1327651309/2500000000 : ℝ)|=(1327651309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1042341327/5000000000 : ℝ)|^1045 ≤ (12534145765619/100000000000000 : ℝ)^789
        have hw : |(-1042341327/5000000000 : ℝ)|=(1042341327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080063627/2000000000 : ℝ)|^1045 ≤ (2210903415411/5000000000000 : ℝ)^789
        have hw : |(1080063627/2000000000 : ℝ)|=(1080063627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s4_6 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5310605071/10000000000 : ℝ)*x 0 + (2700159011/5000000000 : ℝ)*x 1 + (-2084683029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310605071/10000000000 : ℝ)^1045 ≤ (43247784141003/100000000000000 : ℝ)^789 := by
    have hnat : (5310605071 : ℕ)^1045*100000000000000^789 ≤ 43247784141003^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310605071 10000000000 43247784141003 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700159011/5000000000 : ℝ)^1045 ≤ (22109033541381/50000000000000 : ℝ)^789 := by
    have hnat : (2700159011 : ℕ)^1045*50000000000000^789 ≤ 22109033541381^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700159011 5000000000 22109033541381 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084683029/10000000000 : ℝ)^1045 ≤ (12534148751863/100000000000000 : ℝ)^789 := by
    have hnat : (2084683029 : ℕ)^1045*100000000000000^789 ≤ 12534148751863^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084683029 10000000000 12534148751863 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310605071/10000000000 : ℝ), (2700159011/5000000000 : ℝ), (-2084683029/10000000000 : ℝ)] ![(43247784141003/100000000000000 : ℝ), (22109033541381/50000000000000 : ℝ), (12534148751863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310605071/10000000000 : ℝ)|^1045 ≤ (43247784141003/100000000000000 : ℝ)^789
        have hw : |(5310605071/10000000000 : ℝ)|=(5310605071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700159011/5000000000 : ℝ)|^1045 ≤ (22109033541381/50000000000000 : ℝ)^789
        have hw : |(2700159011/5000000000 : ℝ)|=(2700159011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084683029/10000000000 : ℝ)|^1045 ≤ (12534148751863/100000000000000 : ℝ)^789
        have hw : |(-2084683029/10000000000 : ℝ)|=(2084683029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s4_7 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (34068367/78125000 : ℝ)*x 0 + (2252210149/5000000000 : ℝ)*x 1 + (422164333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34068367/78125000 : ℝ)^1045 ≤ (33312931937567/100000000000000 : ℝ)^789 := by
    have hnat : (34068367 : ℕ)^1045*100000000000000^789 ≤ 33312931937567^789*78125000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34068367 78125000 33312931937567 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252210149/5000000000 : ℝ)^1045 ≤ (17387138979843/50000000000000 : ℝ)^789 := by
    have hnat : (2252210149 : ℕ)^1045*50000000000000^789 ≤ 17387138979843^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252210149 5000000000 17387138979843 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422164333/1000000000 : ℝ)^1045 ≤ (7978197522091/25000000000000 : ℝ)^789 := by
    have hnat : (422164333 : ℕ)^1045*25000000000000^789 ≤ 7978197522091^789*1000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422164333 1000000000 7978197522091 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34068367/78125000 : ℝ), (2252210149/5000000000 : ℝ), (422164333/1000000000 : ℝ)] ![(33312931937567/100000000000000 : ℝ), (17387138979843/50000000000000 : ℝ), (7978197522091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34068367/78125000 : ℝ)|^1045 ≤ (33312931937567/100000000000000 : ℝ)^789
        have hw : |(34068367/78125000 : ℝ)|=(34068367/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252210149/5000000000 : ℝ)|^1045 ≤ (17387138979843/50000000000000 : ℝ)^789
        have hw : |(2252210149/5000000000 : ℝ)|=(2252210149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422164333/1000000000 : ℝ)|^1045 ≤ (7978197522091/25000000000000 : ℝ)^789
        have hw : |(422164333/1000000000 : ℝ)|=(422164333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1167_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5611/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14777/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2677/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14777/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2677/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14777/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2677/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14777/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2677/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14777/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2677/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14777/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2677/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2677/25000 : ℝ) ^ (8359/2048 : ℝ) ≤ (10957538099743737/100000000000000000000 : ℝ) := by
    have hpowers : (2677/25000 : ℝ)^8359 ≤ (10957538099743737/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2677 : ℕ)^8359*100000000000000000000^2048 ≤ 10957538099743737^2048*25000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2677 25000 10957538099743737 100000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2677/25000 : ℝ)) (X := (10957538099743737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14777/100000 : ℝ) ^ (8359/2048 : ℝ) ≤ (40797231486467113/100000000000000000000 : ℝ) := by
    have hpowers : (14777/100000 : ℝ)^8359 ≤ (40797231486467113/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14777 : ℕ)^8359*100000000000000000000^2048 ≤ 40797231486467113^2048*100000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14777 100000 40797231486467113 100000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14777/100000 : ℝ)) (X := (40797231486467113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010957538099743737/50000000000000000000 : ℝ) ≤ (10000536886750703/10000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (50010957538099743737/50000000000000000000 : ℝ)^2048 ≤ (10000536886750703/10000000000000000 : ℝ)^8359 := by
      have hnat : (50010957538099743737 : ℕ)^2048*10000000000000000^8359 ≤ 10000536886750703^8359*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010957538099743737 50000000000000000000 10000536886750703 10000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000536886750703/10000000000000000 : ℝ)) (X := (50010957538099743737/50000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2001035095391724217/2000000000000000000 : ℝ) ≤ (5000633886027481/5000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (2001035095391724217/2000000000000000000 : ℝ)^2048 ≤ (5000633886027481/5000000000000000 : ℝ)^8359 := by
      have hnat : (2001035095391724217 : ℕ)^2048*5000000000000000^8359 ≤ 5000633886027481^8359*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001035095391724217 2000000000000000000 5000633886027481 5000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000633886027481/5000000000000000 : ℝ)) (X := (2001035095391724217/2000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040797231486467113/50000000000000000000 : ℝ) ≤ (10001998657359221/10000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (50040797231486467113/50000000000000000000 : ℝ)^2048 ≤ (10001998657359221/10000000000000000 : ℝ)^8359 := by
      have hnat : (50040797231486467113 : ℕ)^2048*10000000000000000^8359 ≤ 10001998657359221^8359*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040797231486467113 50000000000000000000 10001998657359221 10000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001998657359221/10000000000000000 : ℝ)) (X := (50040797231486467113/50000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10957538099743737/100000000000000000000 : ℝ) ≤ ((40676531952512599763/40690000000000000000 : ℝ)+2*(730885304259/406900000000000 : ℝ)*(2677/25000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (40676531952512599763/40690000000000000000 : ℝ)+2*(730885304259/406900000000000 : ℝ)*(2677/25000 : ℝ)=(10000536886750703/10000000000000000 : ℝ) by norm_num, show 1+2*(10957538099743737/100000000000000000000 : ℝ)=(50010957538099743737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40797231486467113/100000000000000000000 : ℝ)+(10957538099743737/100000000000000000000 : ℝ) ≤ ((40676531952512599763/40690000000000000000 : ℝ)+(730885304259/406900000000000 : ℝ)*((14777/100000 : ℝ)+(2677/25000 : ℝ)))^(8359/2048 : ℝ) := by
    rw [show (40676531952512599763/40690000000000000000 : ℝ)+(730885304259/406900000000000 : ℝ)*((14777/100000 : ℝ)+(2677/25000 : ℝ))=(5000633886027481/5000000000000000 : ℝ) by norm_num, show 1+(40797231486467113/100000000000000000000 : ℝ)+(10957538099743737/100000000000000000000 : ℝ)=(2001035095391724217/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40797231486467113/100000000000000000000 : ℝ) ≤ ((40676531952512599763/40690000000000000000 : ℝ)+2*(730885304259/406900000000000 : ℝ)*(14777/100000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (40676531952512599763/40690000000000000000 : ℝ)+2*(730885304259/406900000000000 : ℝ)*(14777/100000 : ℝ)=(10001998657359221/10000000000000000 : ℝ) by norm_num, show 1+2*(40797231486467113/100000000000000000000 : ℝ)=(50040797231486467113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40676531952512599763/40690000000000000000 : ℝ)*(X 1 0+X 2 0)+(730885304259/406900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (2677/25000 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (40676531952512599763/40690000000000000000 : ℝ)) (alpha := (730885304259/406900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40676531952512599763/40690000000000000000 : ℝ)*(X 0 1+X 2 1)+(730885304259/406900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (2677/25000 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (40676531952512599763/40690000000000000000 : ℝ)) (alpha := (730885304259/406900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40676531952512599763/40690000000000000000 : ℝ)*(X 0 2+X 1 2)+(730885304259/406900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (2677/25000 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (40676531952512599763/40690000000000000000 : ℝ)) (alpha := (730885304259/406900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2154256857/10000000000 : ℝ)*X 0 0+(2700360981/5000000000 : ℝ)*X 0 1+(657309133/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673354273/5000000000 : ℝ)*X 1 0+(-2226527843/10000000000 : ℝ)*X 1 1+(5258473223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346708387/10000000000 : ℝ)*X 2 0+(2629236633/5000000000 : ℝ)*X 2 1+(-1113263999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((109018431/250000000 : ℝ)*X 0 0+(2110417899/5000000000 : ℝ)*X 0 1+(1126306141/2500000000 : ℝ)*X 0 2+(109018431/250000000 : ℝ)*X 1 0+(2110417899/5000000000 : ℝ)*X 1 1+(1126306141/2500000000 : ℝ)*X 1 2+(109018431/250000000 : ℝ)*X 2 0+(2110417899/5000000000 : ℝ)*X 2 1+(1126306141/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-3366037/15625000 : ℝ)*X 0 0+(2629437587/5000000000 : ℝ)*X 0 1+(1080063649/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327651309/2500000000 : ℝ)*X 1 0+(-1042341327/5000000000 : ℝ)*X 1 1+(1080063627/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310605071/10000000000 : ℝ)*X 2 0+(2700159011/5000000000 : ℝ)*X 2 1+(-2084683029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34068367/78125000 : ℝ)*X 0 0+(2252210149/5000000000 : ℝ)*X 0 1+(422164333/1000000000 : ℝ)*X 0 2+(34068367/78125000 : ℝ)*X 1 0+(2252210149/5000000000 : ℝ)*X 1 1+(422164333/1000000000 : ℝ)*X 1 2+(34068367/78125000 : ℝ)*X 2 0+(2252210149/5000000000 : ℝ)*X 2 1+(422164333/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2988522557087660390646729069/508625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1358474763/100000000000000 : ℝ)*(base19) + (67741147/6250000000000 : ℝ)*(base23) + (24593881/100000000000000 : ℝ)*(upper2) + (62168811/20000000000000 : ℝ)*(upper3) + (7455769/12500000000000 : ℝ)*(upper4) + (2636589884053979/50000000000000 : ℝ)*(major0) + (2636589884053979/50000000000000 : ℝ)*(major1) + (2636589884053979/50000000000000 : ℝ)*(major2) + (7029977459568293/100000000000000 : ℝ)*(sp0) + (3515003738691057/50000000000000 : ℝ)*(sp1) + (281200310079941/4000000000000 : ℝ)*(sp2) + (219770585472761/6250000000000 : ℝ)*(sp3) + (3922036073/12500000000000 : ℝ)*(sp4) + (21136938539/100000000000000 : ℝ)*(sp7) + (703270100900543/20000000000000 : ℝ)*(f.failure) + (7030008835856877/100000000000000 : ℝ)*(f.sum) + (22769750174487/20345000000000000000000000000 : ℝ)*base65 + (1984479177226706977/2034500000000000000000000000000000 : ℝ)*base67 + (7146641633443706977/2034500000000000000000000000000000 : ℝ)*base69 + (43086863358135293023/2034500000000000000000000000000000 : ℝ)*base72 + (27686073539581/10172500000000000000000000000 : ℝ)*base73 + (35143887282088706977/2034500000000000000000000000000000 : ℝ)*base75 + (19987147268745206977/2034500000000000000000000000000000 : ℝ)*base77 + (26230087339430706977/2034500000000000000000000000000000 : ℝ)*base79 + (41300507422679/10172500000000000000000000000 : ℝ)*base82 + (9507523/1000000000000000000000 : ℝ)*base89 + (9507523/1000000000000000000000 : ℝ)*base91 + (9507523/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56380167554974670547234387/50862500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128872839/12500000000000 : ℝ)*(base19) + (209275987/25000000000000 : ℝ)*(base23) + (342079/400000000000 : ℝ)*(upper2) + (5657423/6250000000000 : ℝ)*(upper5) + (265158708480683/5000000000000 : ℝ)*(major0) + (265158708480683/5000000000000 : ℝ)*(major1) + (265158708480683/5000000000000 : ℝ)*(major2) + (491847687/6250000000000 : ℝ)*(sp0) + (1790953363/5000000000000 : ℝ)*(sp1) + (3981110011/25000000000000 : ℝ)*(sp2) + (141399771129167/2000000000000 : ℝ)*(sp4) + (706995957597137/10000000000000 : ℝ)*(sp5) + (141399593289547/2000000000000 : ℝ)*(sp6) + (3536351876256569/100000000000000 : ℝ)*(sp7) + (3536351876256569/100000000000000 : ℝ)*(f.failure) + (3534998213010671/50000000000000 : ℝ)*(f.sum) + (153836522803/1017250000000000000000000000 : ℝ)*base66 + (3380517824257121871/203450000000000000000000000000000 : ℝ)*base68 + (1322317372642021871/203450000000000000000000000000000 : ℝ)*base70 + (1687261386032778129/203450000000000000000000000000000 : ℝ)*base71 + (353623121783/81380000000000000000000000 : ℝ)*base74 + (5437486421929421871/203450000000000000000000000000000 : ℝ)*base76 + (125314051480321871/203450000000000000000000000000000 : ℝ)*base78 + (2850089535347121871/203450000000000000000000000000000 : ℝ)*base80 + (328307086717/508625000000000000000000000 : ℝ)*base81 + (525909/5000000000000000000000 : ℝ)*base89 + (525909/5000000000000000000000 : ℝ)*base91 + (525909/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1167_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1167_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1167_s5_0 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154843033/10000000000 : ℝ)*x 0 + (2697131917/5000000000 : ℝ)*x 1 + (5264546131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154843033/10000000000 : ℝ)^1045 ≤ (13095882897499/100000000000000 : ℝ)^789 := by
    have hnat : (2154843033 : ℕ)^1045*100000000000000^789 ≤ 13095882897499^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154843033 10000000000 13095882897499 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697131917/5000000000 : ℝ)^1045 ≤ (44152422847299/100000000000000 : ℝ)^789 := by
    have hnat : (2697131917 : ℕ)^1045*100000000000000^789 ≤ 44152422847299^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697131917 5000000000 44152422847299 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264546131/10000000000 : ℝ)^1045 ≤ (42751694239509/100000000000000 : ℝ)^789 := by
    have hnat : (5264546131 : ℕ)^1045*100000000000000^789 ≤ 42751694239509^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264546131 10000000000 42751694239509 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154843033/10000000000 : ℝ), (2697131917/5000000000 : ℝ), (5264546131/10000000000 : ℝ)] ![(13095882897499/100000000000000 : ℝ), (44152422847299/100000000000000 : ℝ), (42751694239509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154843033/10000000000 : ℝ)|^1045 ≤ (13095882897499/100000000000000 : ℝ)^789
        have hw : |(-2154843033/10000000000 : ℝ)|=(2154843033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697131917/5000000000 : ℝ)|^1045 ≤ (44152422847299/100000000000000 : ℝ)^789
        have hw : |(2697131917/5000000000 : ℝ)|=(2697131917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264546131/10000000000 : ℝ)|^1045 ≤ (42751694239509/100000000000000 : ℝ)^789
        have hw : |(5264546131/10000000000 : ℝ)|=(5264546131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s5_1 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345084349/10000000000 : ℝ)*x 0 + (-444131209/2000000000 : ℝ)*x 1 + (5264546049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345084349/10000000000 : ℝ)^1045 ≤ (4362006768137/10000000000000 : ℝ)^789 := by
    have hnat : (5345084349 : ℕ)^1045*10000000000000^789 ≤ 4362006768137^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345084349 10000000000 4362006768137 10000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444131209/2000000000 : ℝ)^1045 ≤ (13628238954621/100000000000000 : ℝ)^789 := by
    have hnat : (444131209 : ℕ)^1045*100000000000000^789 ≤ 13628238954621^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444131209 2000000000 13628238954621 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264546049/10000000000 : ℝ)^1045 ≤ (10687923339389/25000000000000 : ℝ)^789 := by
    have hnat : (5264546049 : ℕ)^1045*25000000000000^789 ≤ 10687923339389^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264546049 10000000000 10687923339389 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345084349/10000000000 : ℝ), (-444131209/2000000000 : ℝ), (5264546049/10000000000 : ℝ)] ![(4362006768137/10000000000000 : ℝ), (13628238954621/100000000000000 : ℝ), (10687923339389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345084349/10000000000 : ℝ)|^1045 ≤ (4362006768137/10000000000000 : ℝ)^789
        have hw : |(5345084349/10000000000 : ℝ)|=(5345084349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-444131209/2000000000 : ℝ)|^1045 ≤ (13628238954621/100000000000000 : ℝ)^789
        have hw : |(-444131209/2000000000 : ℝ)|=(444131209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264546049/10000000000 : ℝ)|^1045 ≤ (10687923339389/25000000000000 : ℝ)^789
        have hw : |(5264546049/10000000000 : ℝ)|=(5264546049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s5_2 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345084263/10000000000 : ℝ)*x 0 + (131613649/250000000 : ℝ)*x 1 + (-555164069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345084263/10000000000 : ℝ)^1045 ≤ (43620066751827/100000000000000 : ℝ)^789 := by
    have hnat : (5345084263 : ℕ)^1045*100000000000000^789 ≤ 43620066751827^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345084263 10000000000 43620066751827 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131613649/250000000 : ℝ)^1045 ≤ (21375846200157/50000000000000 : ℝ)^789 := by
    have hnat : (131613649 : ℕ)^1045*50000000000000^789 ≤ 21375846200157^789*250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131613649 250000000 21375846200157 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555164069/2500000000 : ℝ)^1045 ≤ (13628240832249/100000000000000 : ℝ)^789 := by
    have hnat : (555164069 : ℕ)^1045*100000000000000^789 ≤ 13628240832249^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555164069 2500000000 13628240832249 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345084263/10000000000 : ℝ), (131613649/250000000 : ℝ), (-555164069/2500000000 : ℝ)] ![(43620066751827/100000000000000 : ℝ), (21375846200157/50000000000000 : ℝ), (13628240832249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345084263/10000000000 : ℝ)|^1045 ≤ (43620066751827/100000000000000 : ℝ)^789
        have hw : |(5345084263/10000000000 : ℝ)|=(5345084263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131613649/250000000 : ℝ)|^1045 ≤ (21375846200157/50000000000000 : ℝ)^789
        have hw : |(131613649/250000000 : ℝ)|=(131613649/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-555164069/2500000000 : ℝ)|^1045 ≤ (13628240832249/100000000000000 : ℝ)^789
        have hw : |(-555164069/2500000000 : ℝ)|=(555164069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s5_3 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4361078903/10000000000 : ℝ)*x 0 + (423331773/1000000000 : ℝ)*x 1 + (2246327153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361078903/10000000000 : ℝ)^1045 ≤ (8329062478567/25000000000000 : ℝ)^789 := by
    have hnat : (4361078903 : ℕ)^1045*25000000000000^789 ≤ 8329062478567^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361078903 10000000000 8329062478567 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423331773/1000000000 : ℝ)^1045 ≤ (3202972703919/10000000000000 : ℝ)^789 := by
    have hnat : (423331773 : ℕ)^1045*10000000000000^789 ≤ 3202972703919^789*1000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423331773 1000000000 3202972703919 10000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246327153/5000000000 : ℝ)^1045 ≤ (8663505759127/25000000000000 : ℝ)^789 := by
    have hnat : (2246327153 : ℕ)^1045*25000000000000^789 ≤ 8663505759127^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246327153 5000000000 8663505759127 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361078903/10000000000 : ℝ), (423331773/1000000000 : ℝ), (2246327153/5000000000 : ℝ)] ![(8329062478567/25000000000000 : ℝ), (3202972703919/10000000000000 : ℝ), (8663505759127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361078903/10000000000 : ℝ)|^1045 ≤ (8329062478567/25000000000000 : ℝ)^789
        have hw : |(4361078903/10000000000 : ℝ)|=(4361078903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423331773/1000000000 : ℝ)|^1045 ≤ (3202972703919/10000000000000 : ℝ)^789
        have hw : |(423331773/1000000000 : ℝ)|=(423331773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246327153/5000000000 : ℝ)|^1045 ≤ (8663505759127/25000000000000 : ℝ)^789
        have hw : |(2246327153/5000000000 : ℝ)|=(2246327153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s5_4 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077424259/5000000000 : ℝ)*x 0 + (1316220111/2500000000 : ℝ)*x 1 + (674241009/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077424259/5000000000 : ℝ)^1045 ≤ (327398176199/2500000000000 : ℝ)^789 := by
    have hnat : (1077424259 : ℕ)^1045*2500000000000^789 ≤ 327398176199^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077424259 5000000000 327398176199 2500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316220111/2500000000 : ℝ)^1045 ≤ (2672205624309/6250000000000 : ℝ)^789 := by
    have hnat : (1316220111 : ℕ)^1045*6250000000000^789 ≤ 2672205624309^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316220111 2500000000 2672205624309 6250000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674241009/1250000000 : ℝ)^1045 ≤ (44148782952757/100000000000000 : ℝ)^789 := by
    have hnat : (674241009 : ℕ)^1045*100000000000000^789 ≤ 44148782952757^789*1250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674241009 1250000000 44148782952757 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077424259/5000000000 : ℝ), (1316220111/2500000000 : ℝ), (674241009/1250000000 : ℝ)] ![(327398176199/2500000000000 : ℝ), (2672205624309/6250000000000 : ℝ), (44148782952757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077424259/5000000000 : ℝ)|^1045 ≤ (327398176199/2500000000000 : ℝ)^789
        have hw : |(-1077424259/5000000000 : ℝ)|=(1077424259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316220111/2500000000 : ℝ)|^1045 ≤ (2672205624309/6250000000000 : ℝ)^789
        have hw : |(1316220111/2500000000 : ℝ)|=(1316220111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674241009/1250000000 : ℝ)|^1045 ≤ (44148782952757/100000000000000 : ℝ)^789
        have hw : |(674241009/1250000000 : ℝ)|=(674241009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s5_5 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312159823/10000000000 : ℝ)*x 0 + (-1045637101/5000000000 : ℝ)*x 1 + (5393928009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312159823/10000000000 : ℝ)^1045 ≤ (43264554443307/100000000000000 : ℝ)^789 := by
    have hnat : (5312159823 : ℕ)^1045*100000000000000^789 ≤ 43264554443307^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312159823 10000000000 43264554443307 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045637101/5000000000 : ℝ)^1045 ≤ (12586663266709/100000000000000 : ℝ)^789 := by
    have hnat : (1045637101 : ℕ)^1045*100000000000000^789 ≤ 12586663266709^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045637101 5000000000 12586663266709 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393928009/10000000000 : ℝ)^1045 ≤ (220743911349/500000000000 : ℝ)^789 := by
    have hnat : (5393928009 : ℕ)^1045*500000000000^789 ≤ 220743911349^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393928009 10000000000 220743911349 500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312159823/10000000000 : ℝ), (-1045637101/5000000000 : ℝ), (5393928009/10000000000 : ℝ)] ![(43264554443307/100000000000000 : ℝ), (12586663266709/100000000000000 : ℝ), (220743911349/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312159823/10000000000 : ℝ)|^1045 ≤ (43264554443307/100000000000000 : ℝ)^789
        have hw : |(5312159823/10000000000 : ℝ)|=(5312159823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1045637101/5000000000 : ℝ)|^1045 ≤ (12586663266709/100000000000000 : ℝ)^789
        have hw : |(-1045637101/5000000000 : ℝ)|=(1045637101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393928009/10000000000 : ℝ)|^1045 ≤ (220743911349/500000000000 : ℝ)^789
        have hw : |(5393928009/10000000000 : ℝ)|=(5393928009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s5_6 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312159921/10000000000 : ℝ)*x 0 + (5393927947/10000000000 : ℝ)*x 1 + (-418254831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312159921/10000000000 : ℝ)^1045 ≤ (43264555500433/100000000000000 : ℝ)^789 := by
    have hnat : (5312159921 : ℕ)^1045*100000000000000^789 ≤ 43264555500433^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312159921 10000000000 43264555500433 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393927947/10000000000 : ℝ)^1045 ≤ (11037195399421/25000000000000 : ℝ)^789 := by
    have hnat : (5393927947 : ℕ)^1045*25000000000000^789 ≤ 11037195399421^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393927947 10000000000 11037195399421 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418254831/2000000000 : ℝ)^1045 ≤ (251733257841/2000000000000 : ℝ)^789 := by
    have hnat : (418254831 : ℕ)^1045*2000000000000^789 ≤ 251733257841^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418254831 2000000000 251733257841 2000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312159921/10000000000 : ℝ), (5393927947/10000000000 : ℝ), (-418254831/2000000000 : ℝ)] ![(43264555500433/100000000000000 : ℝ), (11037195399421/25000000000000 : ℝ), (251733257841/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312159921/10000000000 : ℝ)|^1045 ≤ (43264555500433/100000000000000 : ℝ)^789
        have hw : |(5312159921/10000000000 : ℝ)|=(5312159921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393927947/10000000000 : ℝ)|^1045 ≤ (11037195399421/25000000000000 : ℝ)^789
        have hw : |(5393927947/10000000000 : ℝ)|=(5393927947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418254831/2000000000 : ℝ)|^1045 ≤ (251733257841/2000000000000 : ℝ)^789
        have hw : |(-418254831/2000000000 : ℝ)|=(418254831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s5_7 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4361089311/10000000000 : ℝ)*x 0 + (1122996339/2500000000 : ℝ)*x 1 + (4233989167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361089311/10000000000 : ℝ)^1045 ≤ (33316355224097/100000000000000 : ℝ)^789 := by
    have hnat : (4361089311 : ℕ)^1045*100000000000000^789 ≤ 33316355224097^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361089311 10000000000 33316355224097 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122996339/2500000000 : ℝ)^1045 ≤ (1385887562633/4000000000000 : ℝ)^789 := by
    have hnat : (1122996339 : ℕ)^1045*4000000000000^789 ≤ 1385887562633^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122996339 2500000000 1385887562633 4000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233989167/10000000000 : ℝ)^1045 ≤ (1001139240367/3125000000000 : ℝ)^789 := by
    have hnat : (4233989167 : ℕ)^1045*3125000000000^789 ≤ 1001139240367^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233989167 10000000000 1001139240367 3125000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361089311/10000000000 : ℝ), (1122996339/2500000000 : ℝ), (4233989167/10000000000 : ℝ)] ![(33316355224097/100000000000000 : ℝ), (1385887562633/4000000000000 : ℝ), (1001139240367/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361089311/10000000000 : ℝ)|^1045 ≤ (33316355224097/100000000000000 : ℝ)^789
        have hw : |(4361089311/10000000000 : ℝ)|=(4361089311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122996339/2500000000 : ℝ)|^1045 ≤ (1385887562633/4000000000000 : ℝ)^789
        have hw : |(1122996339/2500000000 : ℝ)|=(1122996339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233989167/10000000000 : ℝ)|^1045 ≤ (1001139240367/3125000000000 : ℝ)^789
        have hw : |(4233989167/10000000000 : ℝ)|=(4233989167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1167_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11351/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14099/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5611/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5611/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5611/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5611/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5611/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5611/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5611/50000 : ℝ) ^ (8359/2048 : ℝ) ≤ (3317118415667759/25000000000000000000 : ℝ) := by
    have hpowers : (5611/50000 : ℝ)^8359 ≤ (3317118415667759/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5611 : ℕ)^8359*25000000000000000000^2048 ≤ 3317118415667759^2048*50000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5611 50000 3317118415667759 25000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5611/50000 : ℝ)) (X := (3317118415667759/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8359/2048 : ℝ) ≤ (35016087016171603/100000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8359 ≤ (35016087016171603/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8359*100000000000000000000^2048 ≤ 35016087016171603^2048*50000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 35016087016171603 100000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (35016087016171603/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503317118415667759/12500000000000000000 : ℝ) ≤ (5000325052186991/5000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (12503317118415667759/12500000000000000000 : ℝ)^2048 ≤ (5000325052186991/5000000000000000 : ℝ)^8359 := by
      have hnat : (12503317118415667759 : ℕ)^2048*5000000000000000^8359 ≤ 5000325052186991^8359*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503317118415667759 12500000000000000000 5000325052186991 5000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000325052186991/5000000000000000 : ℝ)) (X := (12503317118415667759/12500000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048284560678842639/100000000000000000000 : ℝ) ≤ (400047311286507/400000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (100048284560678842639/100000000000000000000 : ℝ)^2048 ≤ (400047311286507/400000000000000 : ℝ)^8359 := by
      have hnat : (100048284560678842639 : ℕ)^2048*400000000000000^8359 ≤ 400047311286507^8359*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048284560678842639 100000000000000000000 400047311286507 400000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400047311286507/400000000000000 : ℝ)) (X := (100048284560678842639/100000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035016087016171603/50000000000000000000 : ℝ) ≤ (1250214432493921/1250000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (50035016087016171603/50000000000000000000 : ℝ)^2048 ≤ (1250214432493921/1250000000000000 : ℝ)^8359 := by
      have hnat : (50035016087016171603 : ℕ)^2048*1250000000000000^8359 ≤ 1250214432493921^8359*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035016087016171603 50000000000000000000 1250214432493921 1250000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250214432493921/1250000000000000 : ℝ)) (X := (50035016087016171603/50000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3317118415667759/25000000000000000000 : ℝ) ≤ ((7527500673521252023/7530000000000000000 : ℝ)+2*(532677788693/301200000000000 : ℝ)*(5611/50000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (7527500673521252023/7530000000000000000 : ℝ)+2*(532677788693/301200000000000 : ℝ)*(5611/50000 : ℝ)=(5000325052186991/5000000000000000 : ℝ) by norm_num, show 1+2*(3317118415667759/25000000000000000000 : ℝ)=(12503317118415667759/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35016087016171603/100000000000000000000 : ℝ)+(3317118415667759/25000000000000000000 : ℝ) ≤ ((7527500673521252023/7530000000000000000 : ℝ)+(532677788693/301200000000000 : ℝ)*((7117/50000 : ℝ)+(5611/50000 : ℝ)))^(8359/2048 : ℝ) := by
    rw [show (7527500673521252023/7530000000000000000 : ℝ)+(532677788693/301200000000000 : ℝ)*((7117/50000 : ℝ)+(5611/50000 : ℝ))=(400047311286507/400000000000000 : ℝ) by norm_num, show 1+(35016087016171603/100000000000000000000 : ℝ)+(3317118415667759/25000000000000000000 : ℝ)=(100048284560678842639/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35016087016171603/100000000000000000000 : ℝ) ≤ ((7527500673521252023/7530000000000000000 : ℝ)+2*(532677788693/301200000000000 : ℝ)*(7117/50000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (7527500673521252023/7530000000000000000 : ℝ)+2*(532677788693/301200000000000 : ℝ)*(7117/50000 : ℝ)=(1250214432493921/1250000000000000 : ℝ) by norm_num, show 1+2*(35016087016171603/100000000000000000000 : ℝ)=(50035016087016171603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7527500673521252023/7530000000000000000 : ℝ)*(X 1 0+X 2 0)+(532677788693/301200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7527500673521252023/7530000000000000000 : ℝ)) (alpha := (532677788693/301200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7527500673521252023/7530000000000000000 : ℝ)*(X 0 1+X 2 1)+(532677788693/301200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7527500673521252023/7530000000000000000 : ℝ)) (alpha := (532677788693/301200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7527500673521252023/7530000000000000000 : ℝ)*(X 0 2+X 1 2)+(532677788693/301200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (7527500673521252023/7530000000000000000 : ℝ)) (alpha := (532677788693/301200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2154843033/10000000000 : ℝ)*X 0 0+(2697131917/5000000000 : ℝ)*X 0 1+(5264546131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345084349/10000000000 : ℝ)*X 1 0+(-444131209/2000000000 : ℝ)*X 1 1+(5264546049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345084263/10000000000 : ℝ)*X 2 0+(131613649/250000000 : ℝ)*X 2 1+(-555164069/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361078903/10000000000 : ℝ)*X 0 0+(423331773/1000000000 : ℝ)*X 0 1+(2246327153/5000000000 : ℝ)*X 0 2+(4361078903/10000000000 : ℝ)*X 1 0+(423331773/1000000000 : ℝ)*X 1 1+(2246327153/5000000000 : ℝ)*X 1 2+(4361078903/10000000000 : ℝ)*X 2 0+(423331773/1000000000 : ℝ)*X 2 1+(2246327153/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1077424259/5000000000 : ℝ)*X 0 0+(1316220111/2500000000 : ℝ)*X 0 1+(674241009/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312159823/10000000000 : ℝ)*X 1 0+(-1045637101/5000000000 : ℝ)*X 1 1+(5393928009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312159921/10000000000 : ℝ)*X 2 0+(5393927947/10000000000 : ℝ)*X 2 1+(-418254831/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361089311/10000000000 : ℝ)*X 0 0+(1122996339/2500000000 : ℝ)*X 0 1+(4233989167/10000000000 : ℝ)*X 0 2+(4361089311/10000000000 : ℝ)*X 1 0+(1122996339/2500000000 : ℝ)*X 1 1+(4233989167/10000000000 : ℝ)*X 1 2+(4361089311/10000000000 : ℝ)*X 2 0+(1122996339/2500000000 : ℝ)*X 2 1+(4233989167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (775991693273272002608711003/62750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1313850473/100000000000000 : ℝ)*(base19) + (1389270297/100000000000000 : ℝ)*(base23) + (83860961/100000000000000 : ℝ)*(lower2) + (120206487/50000000000000 : ℝ)*(upper3) + (190471853/100000000000000 : ℝ)*(lower4) + (2891286577378739/50000000000000 : ℝ)*(major0) + (2891286577378739/50000000000000 : ℝ)*(major1) + (2891286577378739/50000000000000 : ℝ)*(major2) + (7709088499173009/100000000000000 : ℝ)*(sp0) + (9636389756827/125000000000 : ℝ)*(sp1) + (481819483127611/6250000000000 : ℝ)*(sp2) + (964002816723753/25000000000000 : ℝ)*(sp3) + (3077517383/12500000000000 : ℝ)*(sp4) + (21511094479/100000000000000 : ℝ)*(sp7) + (3856032777989491/100000000000000 : ℝ)*(f.failure) + (7709113119312073/100000000000000 : ℝ)*(f.sum) + (2129078857447/7530000000000000000000000000 : ℝ)*base65 + (1403283409545037999/125500000000000000000000000000000 : ℝ)*base67 + (2022138938672037999/125500000000000000000000000000000 : ℝ)*base69 + (1209422179170537999/125500000000000000000000000000000 : ℝ)*base71 + (11317226540393/7530000000000000000000000000 : ℝ)*base74 + (213924130759462001/125500000000000000000000000000000 : ℝ)*base76 + (2420538256826537999/125500000000000000000000000000000 : ℝ)*base77 + (1671504747223962001/125500000000000000000000000000000 : ℝ)*base80 + (17286199795957/7530000000000000000000000000 : ℝ)*base81 + (15868249/5000000000000000000000 : ℝ)*base90 + (15868249/5000000000000000000000 : ℝ)*base92 + (15868249/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35767105712969577575713/5020000000000000000000000000 : ℝ) := by norm_num
    linear_combination (816338913/100000000000000 : ℝ)*(base19) + (50405647/5000000000000 : ℝ)*(base23) + (74118469/100000000000000 : ℝ)*(upper3) + (10716113/50000000000000 : ℝ)*(lower4) + (83136247/50000000000000 : ℝ)*(upper5) + (5812553767647461/100000000000000 : ℝ)*(major0) + (5812553767647461/100000000000000 : ℝ)*(major1) + (5812553767647461/100000000000000 : ℝ)*(major2) + (19560214697/100000000000000 : ℝ)*(sp1) + (1046357813/5000000000000 : ℝ)*(sp2) + (7749082342811047/100000000000000 : ℝ)*(sp4) + (7749061966257437/100000000000000 : ℝ)*(sp5) + (7749060407541847/100000000000000 : ℝ)*(sp6) + (484503119373311/12500000000000 : ℝ)*(sp7) + (484503119373311/12500000000000 : ℝ)*(f.failure) + (7749082342811047/100000000000000 : ℝ)*(f.sum) + (36503449543153/15060000000000000000000000000 : ℝ)*base65 + (1420460162609703799/251000000000000000000000000000000 : ℝ)*base68 + (374377514106296201/251000000000000000000000000000000 : ℝ)*base69 + (1679307992314296201/251000000000000000000000000000000 : ℝ)*base71 + (54006919541867/15060000000000000000000000000 : ℝ)*base74 + (1939070335095703799/251000000000000000000000000000000 : ℝ)*base76 + (1199692282001296201/251000000000000000000000000000000 : ℝ)*base77 + (325985415700703799/251000000000000000000000000000000 : ℝ)*base80 + (70804653213587/15060000000000000000000000000 : ℝ)*base82 + (7950771/625000000000000000000 : ℝ)*base89 + (7950771/625000000000000000000 : ℝ)*base91 + (7950771/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1167_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1167_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1167_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16429/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1167_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1167_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1167_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16429/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1167_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
