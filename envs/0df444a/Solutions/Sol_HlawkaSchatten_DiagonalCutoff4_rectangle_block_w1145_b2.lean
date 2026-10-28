-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1145_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:33:30.577344+00:00
-- url     : https://prove2.me/submissions/0f673ac7-75e3-41ea-aff8-fcd430d4c7b8

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
theorem support_rectangle_w1145_s6_0 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2165421377/10000000000 : ℝ)*x 0 + (5393319751/10000000000 : ℝ)*x 1 + (65818353/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165421377/10000000000 : ℝ)^4169 ≤ (3289558208909/25000000000000 : ℝ)^3145 := by
    have hnat : (2165421377 : ℕ)^4169*25000000000000^3145 ≤ 3289558208909^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165421377 10000000000 3289558208909 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393319751/10000000000 : ℝ)^4169 ≤ (22055634943719/50000000000000 : ℝ)^3145 := by
    have hnat : (5393319751 : ℕ)^4169*50000000000000^3145 ≤ 22055634943719^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393319751 10000000000 22055634943719 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65818353/125000000 : ℝ)^4169 ≤ (1335328039541/3125000000000 : ℝ)^3145 := by
    have hnat : (65818353 : ℕ)^4169*3125000000000^3145 ≤ 1335328039541^3145*125000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65818353 125000000 1335328039541 3125000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2165421377/10000000000 : ℝ), (5393319751/10000000000 : ℝ), (65818353/125000000 : ℝ)] ![(3289558208909/25000000000000 : ℝ), (22055634943719/50000000000000 : ℝ), (1335328039541/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2165421377/10000000000 : ℝ)|^4169 ≤ (3289558208909/25000000000000 : ℝ)^3145
        have hw : |(-2165421377/10000000000 : ℝ)|=(2165421377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393319751/10000000000 : ℝ)|^4169 ≤ (22055634943719/50000000000000 : ℝ)^3145
        have hw : |(5393319751/10000000000 : ℝ)|=(5393319751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65818353/125000000 : ℝ)|^4169 ≤ (1335328039541/3125000000000 : ℝ)^3145
        have hw : |(65818353/125000000 : ℝ)|=(65818353/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s6_1 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41756507/78125000 : ℝ)*x 0 + (-1115136927/5000000000 : ℝ)*x 1 + (5265468239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41756507/78125000 : ℝ)^4169 ≤ (1362073503873/3125000000000 : ℝ)^3145 := by
    have hnat : (41756507 : ℕ)^4169*3125000000000^3145 ≤ 1362073503873^3145*78125000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41756507 78125000 1362073503873 3125000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115136927/5000000000 : ℝ)^4169 ≤ (85519691291/625000000000 : ℝ)^3145 := by
    have hnat : (1115136927 : ℕ)^4169*625000000000^3145 ≤ 85519691291^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115136927 5000000000 85519691291 625000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265468239/10000000000 : ℝ)^4169 ≤ (8546099450911/20000000000000 : ℝ)^3145 := by
    have hnat : (5265468239 : ℕ)^4169*20000000000000^3145 ≤ 8546099450911^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265468239 10000000000 8546099450911 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41756507/78125000 : ℝ), (-1115136927/5000000000 : ℝ), (5265468239/10000000000 : ℝ)] ![(1362073503873/3125000000000 : ℝ), (85519691291/625000000000 : ℝ), (8546099450911/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41756507/78125000 : ℝ)|^4169 ≤ (1362073503873/3125000000000 : ℝ)^3145
        have hw : |(41756507/78125000 : ℝ)|=(41756507/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115136927/5000000000 : ℝ)|^4169 ≤ (85519691291/625000000000 : ℝ)^3145
        have hw : |(-1115136927/5000000000 : ℝ)|=(1115136927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265468239/10000000000 : ℝ)|^4169 ≤ (8546099450911/20000000000000 : ℝ)^3145
        have hw : |(5265468239/10000000000 : ℝ)|=(5265468239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s6_2 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336208219/2500000000 : ℝ)*x 0 + (1053093651/2000000000 : ℝ)*x 1 + (-2230273859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336208219/2500000000 : ℝ)^4169 ≤ (8717270381547/20000000000000 : ℝ)^3145 := by
    have hnat : (1336208219 : ℕ)^4169*20000000000000^3145 ≤ 8717270381547^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336208219 2500000000 8717270381547 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053093651/2000000000 : ℝ)^4169 ≤ (1709219897067/4000000000000 : ℝ)^3145 := by
    have hnat : (1053093651 : ℕ)^4169*4000000000000^3145 ≤ 1709219897067^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053093651 2000000000 1709219897067 4000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230273859/10000000000 : ℝ)^4169 ≤ (1710393830903/12500000000000 : ℝ)^3145 := by
    have hnat : (2230273859 : ℕ)^4169*12500000000000^3145 ≤ 1710393830903^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230273859 10000000000 1710393830903 12500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336208219/2500000000 : ℝ), (1053093651/2000000000 : ℝ), (-2230273859/10000000000 : ℝ)] ![(8717270381547/20000000000000 : ℝ), (1709219897067/4000000000000 : ℝ), (1710393830903/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336208219/2500000000 : ℝ)|^4169 ≤ (8717270381547/20000000000000 : ℝ)^3145
        have hw : |(1336208219/2500000000 : ℝ)|=(1336208219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053093651/2000000000 : ℝ)|^4169 ≤ (1709219897067/4000000000000 : ℝ)^3145
        have hw : |(1053093651/2000000000 : ℝ)|=(1053093651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230273859/10000000000 : ℝ)|^4169 ≤ (1710393830903/12500000000000 : ℝ)^3145
        have hw : |(-2230273859/10000000000 : ℝ)|=(2230273859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s6_3 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364233871/10000000000 : ℝ)*x 0 + (2119412607/5000000000 : ℝ)*x 1 + (4493332157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364233871/10000000000 : ℝ)^4169 ≤ (33316812090469/100000000000000 : ℝ)^3145 := by
    have hnat : (4364233871 : ℕ)^4169*100000000000000^3145 ≤ 33316812090469^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364233871 10000000000 33316812090469 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119412607/5000000000 : ℝ)^4169 ≤ (4006711587479/12500000000000 : ℝ)^3145 := by
    have hnat : (2119412607 : ℕ)^4169*12500000000000^3145 ≤ 4006711587479^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119412607 5000000000 4006711587479 12500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493332157/10000000000 : ℝ)^4169 ≤ (17314747598739/50000000000000 : ℝ)^3145 := by
    have hnat : (4493332157 : ℕ)^4169*50000000000000^3145 ≤ 17314747598739^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493332157 10000000000 17314747598739 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364233871/10000000000 : ℝ), (2119412607/5000000000 : ℝ), (4493332157/10000000000 : ℝ)] ![(33316812090469/100000000000000 : ℝ), (4006711587479/12500000000000 : ℝ), (17314747598739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364233871/10000000000 : ℝ)|^4169 ≤ (33316812090469/100000000000000 : ℝ)^3145
        have hw : |(4364233871/10000000000 : ℝ)|=(4364233871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119412607/5000000000 : ℝ)|^4169 ≤ (4006711587479/12500000000000 : ℝ)^3145
        have hw : |(2119412607/5000000000 : ℝ)|=(2119412607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493332157/10000000000 : ℝ)|^4169 ≤ (17314747598739/50000000000000 : ℝ)^3145
        have hw : |(4493332157/10000000000 : ℝ)|=(4493332157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s6_4 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-433085273/2000000000 : ℝ)*x 0 + (5265791099/10000000000 : ℝ)*x 1 + (1348248923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433085273/2000000000 : ℝ)^4169 ≤ (1315827301407/10000000000000 : ℝ)^3145 := by
    have hnat : (433085273 : ℕ)^4169*10000000000000^3145 ≤ 1315827301407^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433085273 2000000000 1315827301407 10000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265791099/10000000000 : ℝ)^4169 ≤ (4273397046239/10000000000000 : ℝ)^3145 := by
    have hnat : (5265791099 : ℕ)^4169*10000000000000^3145 ≤ 4273397046239^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265791099 10000000000 4273397046239 10000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348248923/2500000000 : ℝ)^4169 ≤ (11026939128171/25000000000000 : ℝ)^3145 := by
    have hnat : (1348248923 : ℕ)^4169*25000000000000^3145 ≤ 11026939128171^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348248923 2500000000 11026939128171 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-433085273/2000000000 : ℝ), (5265791099/10000000000 : ℝ), (1348248923/2500000000 : ℝ)] ![(1315827301407/10000000000000 : ℝ), (4273397046239/10000000000000 : ℝ), (11026939128171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-433085273/2000000000 : ℝ)|^4169 ≤ (1315827301407/10000000000000 : ℝ)^3145
        have hw : |(-433085273/2000000000 : ℝ)|=(433085273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265791099/10000000000 : ℝ)|^4169 ≤ (4273397046239/10000000000000 : ℝ)^3145
        have hw : |(5265791099/10000000000 : ℝ)|=(5265791099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348248923/2500000000 : ℝ)|^4169 ≤ (11026939128171/25000000000000 : ℝ)^3145
        have hw : |(1348248923/2500000000 : ℝ)|=(1348248923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s6_5 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312433961/10000000000 : ℝ)*x 0 + (-525686619/2500000000 : ℝ)*x 1 + (5392995627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312433961/10000000000 : ℝ)^4169 ≤ (8647292833269/20000000000000 : ℝ)^3145 := by
    have hnat : (5312433961 : ℕ)^4169*20000000000000^3145 ≤ 8647292833269^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312433961 10000000000 8647292833269 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525686619/2500000000 : ℝ)^4169 ≤ (12655780005527/100000000000000 : ℝ)^3145 := by
    have hnat : (525686619 : ℕ)^4169*100000000000000^3145 ≤ 12655780005527^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525686619 2500000000 12655780005527 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392995627/10000000000 : ℝ)^4169 ≤ (1764310232319/4000000000000 : ℝ)^3145 := by
    have hnat : (5392995627 : ℕ)^4169*4000000000000^3145 ≤ 1764310232319^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392995627 10000000000 1764310232319 4000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312433961/10000000000 : ℝ), (-525686619/2500000000 : ℝ), (5392995627/10000000000 : ℝ)] ![(8647292833269/20000000000000 : ℝ), (12655780005527/100000000000000 : ℝ), (1764310232319/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312433961/10000000000 : ℝ)|^4169 ≤ (8647292833269/20000000000000 : ℝ)^3145
        have hw : |(5312433961/10000000000 : ℝ)|=(5312433961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525686619/2500000000 : ℝ)|^4169 ≤ (12655780005527/100000000000000 : ℝ)^3145
        have hw : |(-525686619/2500000000 : ℝ)|=(525686619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392995627/10000000000 : ℝ)|^4169 ≤ (1764310232319/4000000000000 : ℝ)^3145
        have hw : |(5392995627/10000000000 : ℝ)|=(5392995627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s6_6 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656217001/5000000000 : ℝ)*x 0 + (5392995551/10000000000 : ℝ)*x 1 + (-525686631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656217001/5000000000 : ℝ)^4169 ≤ (1080911615217/2500000000000 : ℝ)^3145 := by
    have hnat : (2656217001 : ℕ)^4169*2500000000000^3145 ≤ 1080911615217^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656217001 5000000000 1080911615217 2500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392995551/10000000000 : ℝ)^4169 ≤ (5513469373001/12500000000000 : ℝ)^3145 := by
    have hnat : (5392995551 : ℕ)^4169*12500000000000^3145 ≤ 5513469373001^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392995551 10000000000 5513469373001 12500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525686631/2500000000 : ℝ)^4169 ≤ (1581972548561/12500000000000 : ℝ)^3145 := by
    have hnat : (525686631 : ℕ)^4169*12500000000000^3145 ≤ 1581972548561^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525686631 2500000000 1581972548561 12500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656217001/5000000000 : ℝ), (5392995551/10000000000 : ℝ), (-525686631/2500000000 : ℝ)] ![(1080911615217/2500000000000 : ℝ), (5513469373001/12500000000000 : ℝ), (1581972548561/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656217001/5000000000 : ℝ)|^4169 ≤ (1080911615217/2500000000000 : ℝ)^3145
        have hw : |(2656217001/5000000000 : ℝ)|=(2656217001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392995551/10000000000 : ℝ)|^4169 ≤ (5513469373001/12500000000000 : ℝ)^3145
        have hw : |(5392995551/10000000000 : ℝ)|=(5392995551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525686631/2500000000 : ℝ)|^4169 ≤ (1581972548561/12500000000000 : ℝ)^3145
        have hw : |(-525686631/2500000000 : ℝ)|=(525686631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s6_7 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872848729/2000000000 : ℝ)*x 0 + (4492689413/10000000000 : ℝ)*x 1 + (2119735189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872848729/2000000000 : ℝ)^4169 ≤ (33316911000233/100000000000000 : ℝ)^3145 := by
    have hnat : (872848729 : ℕ)^4169*100000000000000^3145 ≤ 33316911000233^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872848729 2000000000 33316911000233 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492689413/10000000000 : ℝ)^4169 ≤ (6924585791353/20000000000000 : ℝ)^3145 := by
    have hnat : (4492689413 : ℕ)^4169*20000000000000^3145 ≤ 6924585791353^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492689413 10000000000 6924585791353 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119735189/5000000000 : ℝ)^4169 ≤ (32060160024921/100000000000000 : ℝ)^3145 := by
    have hnat : (2119735189 : ℕ)^4169*100000000000000^3145 ≤ 32060160024921^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119735189 5000000000 32060160024921 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872848729/2000000000 : ℝ), (4492689413/10000000000 : ℝ), (2119735189/5000000000 : ℝ)] ![(33316911000233/100000000000000 : ℝ), (6924585791353/20000000000000 : ℝ), (32060160024921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872848729/2000000000 : ℝ)|^4169 ≤ (33316911000233/100000000000000 : ℝ)^3145
        have hw : |(872848729/2000000000 : ℝ)|=(872848729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492689413/10000000000 : ℝ)|^4169 ≤ (6924585791353/20000000000000 : ℝ)^3145
        have hw : |(4492689413/10000000000 : ℝ)|=(4492689413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119735189/5000000000 : ℝ)|^4169 ≤ (32060160024921/100000000000000 : ℝ)^3145
        have hw : |(2119735189/5000000000 : ℝ)|=(2119735189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1145_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (227/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7029/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (283/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (283/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (283/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (283/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (283/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (283/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (283/2500 : ℝ) ^ (8337/2048 : ℝ) ≤ (7036671867608981/50000000000000000000 : ℝ) := by
    have hpowers : (283/2500 : ℝ)^8337 ≤ (7036671867608981/50000000000000000000 : ℝ)^2048 := by
      have hnat : (283 : ℕ)^8337*50000000000000000000^2048 ≤ 7036671867608981^2048*2500^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        283 2500 7036671867608981 50000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (283/2500 : ℝ)) (X := (7036671867608981/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1409/10000 : ℝ) ^ (8337/2048 : ℝ) ≤ (8576818396119523/25000000000000000000 : ℝ) := by
    have hpowers : (1409/10000 : ℝ)^8337 ≤ (8576818396119523/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1409 : ℕ)^8337*25000000000000000000^2048 ≤ 8576818396119523^2048*10000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 10000 8576818396119523 25000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/10000 : ℝ)) (X := (8576818396119523/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007036671867608981/25000000000000000000 : ℝ) ≤ (5000345677685619/5000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (25007036671867608981/25000000000000000000 : ℝ)^2048 ≤ (5000345677685619/5000000000000000 : ℝ)^8337 := by
      have hnat : (25007036671867608981 : ℕ)^2048*5000000000000000^8337 ≤ 5000345677685619^8337*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007036671867608981 25000000000000000000 5000345677685619 5000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000345677685619/5000000000000000 : ℝ)) (X := (25007036671867608981/25000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024190308659848027/50000000000000000000 : ℝ) ≤ (10001188262309137/10000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (50024190308659848027/50000000000000000000 : ℝ)^2048 ≤ (10001188262309137/10000000000000000 : ℝ)^8337 := by
      have hnat : (50024190308659848027 : ℕ)^2048*10000000000000000^8337 ≤ 10001188262309137^8337*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024190308659848027 50000000000000000000 10001188262309137 10000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001188262309137/10000000000000000 : ℝ)) (X := (50024190308659848027/50000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508576818396119523/12500000000000000000 : ℝ) ≤ (2500421292311759/2500000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (12508576818396119523/12500000000000000000 : ℝ)^2048 ≤ (2500421292311759/2500000000000000 : ℝ)^8337 := by
      have hnat : (12508576818396119523 : ℕ)^2048*2500000000000000^8337 ≤ 2500421292311759^8337*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508576818396119523 12500000000000000000 2500421292311759 2500000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500421292311759/2500000000000000 : ℝ)) (X := (12508576818396119523/12500000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7036671867608981/50000000000000000000 : ℝ) ≤ ((276906650813042959/277000000000000000 : ℝ)+2*(496906937899/277000000000000 : ℝ)*(283/2500 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (276906650813042959/277000000000000000 : ℝ)+2*(496906937899/277000000000000 : ℝ)*(283/2500 : ℝ)=(5000345677685619/5000000000000000 : ℝ) by norm_num, show 1+2*(7036671867608981/50000000000000000000 : ℝ)=(25007036671867608981/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8576818396119523/25000000000000000000 : ℝ)+(7036671867608981/50000000000000000000 : ℝ) ≤ ((276906650813042959/277000000000000000 : ℝ)+(496906937899/277000000000000 : ℝ)*((1409/10000 : ℝ)+(283/2500 : ℝ)))^(8337/2048 : ℝ) := by
    rw [show (276906650813042959/277000000000000000 : ℝ)+(496906937899/277000000000000 : ℝ)*((1409/10000 : ℝ)+(283/2500 : ℝ))=(10001188262309137/10000000000000000 : ℝ) by norm_num, show 1+(8576818396119523/25000000000000000000 : ℝ)+(7036671867608981/50000000000000000000 : ℝ)=(50024190308659848027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8576818396119523/25000000000000000000 : ℝ) ≤ ((276906650813042959/277000000000000000 : ℝ)+2*(496906937899/277000000000000 : ℝ)*(1409/10000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (276906650813042959/277000000000000000 : ℝ)+2*(496906937899/277000000000000 : ℝ)*(1409/10000 : ℝ)=(2500421292311759/2500000000000000 : ℝ) by norm_num, show 1+2*(8576818396119523/25000000000000000000 : ℝ)=(12508576818396119523/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (276906650813042959/277000000000000000 : ℝ)*(X 1 0+X 2 0)+(496906937899/277000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (276906650813042959/277000000000000000 : ℝ)) (alpha := (496906937899/277000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (276906650813042959/277000000000000000 : ℝ)*(X 0 1+X 2 1)+(496906937899/277000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (276906650813042959/277000000000000000 : ℝ)) (alpha := (496906937899/277000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (276906650813042959/277000000000000000 : ℝ)*(X 0 2+X 1 2)+(496906937899/277000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (276906650813042959/277000000000000000 : ℝ)) (alpha := (496906937899/277000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2165421377/10000000000 : ℝ)*X 0 0+(5393319751/10000000000 : ℝ)*X 0 1+(65818353/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((41756507/78125000 : ℝ)*X 1 0+(-1115136927/5000000000 : ℝ)*X 1 1+(5265468239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336208219/2500000000 : ℝ)*X 2 0+(1053093651/2000000000 : ℝ)*X 2 1+(-2230273859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364233871/10000000000 : ℝ)*X 0 0+(2119412607/5000000000 : ℝ)*X 0 1+(4493332157/10000000000 : ℝ)*X 0 2+(4364233871/10000000000 : ℝ)*X 1 0+(2119412607/5000000000 : ℝ)*X 1 1+(4493332157/10000000000 : ℝ)*X 1 2+(4364233871/10000000000 : ℝ)*X 2 0+(2119412607/5000000000 : ℝ)*X 2 1+(4493332157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-433085273/2000000000 : ℝ)*X 0 0+(5265791099/10000000000 : ℝ)*X 0 1+(1348248923/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312433961/10000000000 : ℝ)*X 1 0+(-525686619/2500000000 : ℝ)*X 1 1+(5392995627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656217001/5000000000 : ℝ)*X 2 0+(5392995551/10000000000 : ℝ)*X 2 1+(-525686631/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872848729/2000000000 : ℝ)*X 0 0+(4492689413/10000000000 : ℝ)*X 0 1+(2119735189/5000000000 : ℝ)*X 0 2+(872848729/2000000000 : ℝ)*X 1 0+(4492689413/10000000000 : ℝ)*X 1 1+(2119735189/5000000000 : ℝ)*X 1 2+(872848729/2000000000 : ℝ)*X 2 0+(4492689413/10000000000 : ℝ)*X 2 1+(2119735189/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24116569454576812351603743/3462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1475363369/100000000000000 : ℝ)*(base19) + (331638713/25000000000000 : ℝ)*(base23) + (31946179/50000000000000 : ℝ)*(lower2) + (23776439/12500000000000 : ℝ)*(upper3) + (88004773/100000000000000 : ℝ)*(upper5) + (1468858007252059/25000000000000 : ℝ)*(major0) + (1468858007252059/25000000000000 : ℝ)*(major1) + (1468858007252059/25000000000000 : ℝ)*(major2) + (7821616633411027/100000000000000 : ℝ)*(sp0) + (782165495511031/10000000000000 : ℝ)*(sp1) + (7821655103918827/100000000000000 : ℝ)*(sp2) + (982296327319309/25000000000000 : ℝ)*(sp3) + (9949265663/25000000000000 : ℝ)*(sp4) + (2760762051/12500000000000 : ℝ)*(sp7) + (982301848843411/25000000000000 : ℝ)*(f.failure) + (7821656430473679/100000000000000 : ℝ)*(f.sum) + (23315035864143/6925000000000000000000000000 : ℝ)*base66 + (8569701501281419/6925000000000000000000000000000 : ℝ)*base68 + (7705960842256419/6925000000000000000000000000000 : ℝ)*base70 + (37941117029056419/6925000000000000000000000000000 : ℝ)*base72 + (2703967031091/3462500000000000000000000000 : ℝ)*base73 + (296841229157693581/6925000000000000000000000000000 : ℝ)*base75 + (136650607028843581/6925000000000000000000000000000 : ℝ)*base77 + (22406599816781419/6925000000000000000000000000000 : ℝ)*base80 + (58897024646693/6925000000000000000000000000 : ℝ)*base82 + (57539/500000000000000000000 : ℝ)*base89 + (57539/500000000000000000000 : ℝ)*base91 + (57539/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26674001021236065130839/6925000000000000000000000000 : ℝ) := by norm_num
    linear_combination (204708497/25000000000000 : ℝ)*(base19) + (89501163/10000000000000 : ℝ)*(base23) + (19856549/100000000000000 : ℝ)*(upper2) + (6096017/12500000000000 : ℝ)*(upper3) + (98010789/100000000000000 : ℝ)*(upper5) + (1476312861726181/25000000000000 : ℝ)*(major0) + (1476312861726181/25000000000000 : ℝ)*(major1) + (1476312861726181/25000000000000 : ℝ)*(major2) + (2718732089/12500000000000 : ℝ)*(sp1) + (18163592481/100000000000000 : ℝ)*(sp2) + (7861353572272657/100000000000000 : ℝ)*(sp4) + (7861331003581957/100000000000000 : ℝ)*(sp5) + (1572266902733709/20000000000000 : ℝ)*(sp6) + (394914919314207/10000000000000 : ℝ)*(sp7) + (394914919314207/10000000000000 : ℝ)*(f.failure) + (7861353572272657/100000000000000 : ℝ)*(f.sum) + (5450258703313/6925000000000000000000000000 : ℝ)*base65 + (100585320682203579/6925000000000000000000000000000 : ℝ)*base67 + (74613101538471421/6925000000000000000000000000000 : ℝ)*base70 + (60304674387153579/6925000000000000000000000000000 : ℝ)*base71 + (1185350548203/1731250000000000000000000000 : ℝ)*base74 + (112172075587246421/6925000000000000000000000000000 : ℝ)*base76 + (44145652129428579/6925000000000000000000000000000 : ℝ)*base77 + (16475945123771421/6925000000000000000000000000000 : ℝ)*base80 + (29016971486987/6925000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1379057/200000000000000000000 : ℝ)*base90 + (1379057/200000000000000000000 : ℝ)*base92 + (1379057/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1145_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1145_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1145_s7_0 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2165450557/10000000000 : ℝ)*x 0 + (2696501661/5000000000 : ℝ)*x 1 + (1053153059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165450557/10000000000 : ℝ)^4169 ≤ (1315846788151/10000000000000 : ℝ)^3145 := by
    have hnat : (2165450557 : ℕ)^4169*10000000000000^3145 ≤ 1315846788151^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165450557 10000000000 1315846788151 10000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696501661/5000000000 : ℝ)^4169 ≤ (44107839234637/100000000000000 : ℝ)^3145 := by
    have hnat : (2696501661 : ℕ)^4169*100000000000000^3145 ≤ 44107839234637^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696501661 5000000000 44107839234637 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053153059/2000000000 : ℝ)^4169 ≤ (42733692870003/100000000000000 : ℝ)^3145 := by
    have hnat : (1053153059 : ℕ)^4169*100000000000000^3145 ≤ 42733692870003^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053153059 2000000000 42733692870003 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2165450557/10000000000 : ℝ), (2696501661/5000000000 : ℝ), (1053153059/2000000000 : ℝ)] ![(1315846788151/10000000000000 : ℝ), (44107839234637/100000000000000 : ℝ), (42733692870003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2165450557/10000000000 : ℝ)|^4169 ≤ (1315846788151/10000000000000 : ℝ)^3145
        have hw : |(-2165450557/10000000000 : ℝ)|=(2165450557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696501661/5000000000 : ℝ)|^4169 ≤ (44107839234637/100000000000000 : ℝ)^3145
        have hw : |(2696501661/5000000000 : ℝ)|=(2696501661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053153059/2000000000 : ℝ)|^4169 ≤ (42733692870003/100000000000000 : ℝ)^3145
        have hw : |(1053153059/2000000000 : ℝ)|=(1053153059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s7_1 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672376371/5000000000 : ℝ)*x 0 + (-557496861/2500000000 : ℝ)*x 1 + (1053153061/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672376371/5000000000 : ℝ)^4169 ≤ (8717097131487/20000000000000 : ℝ)^3145 := by
    have hnat : (2672376371 : ℕ)^4169*20000000000000^3145 ≤ 8717097131487^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672376371 5000000000 8717097131487 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557496861/2500000000 : ℝ)^4169 ≤ (2736164269003/20000000000000 : ℝ)^3145 := by
    have hnat : (557496861 : ℕ)^4169*20000000000000^3145 ≤ 2736164269003^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557496861 2500000000 2736164269003 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053153061/2000000000 : ℝ)^4169 ≤ (42733692977581/100000000000000 : ℝ)^3145 := by
    have hnat : (1053153061 : ℕ)^4169*100000000000000^3145 ≤ 42733692977581^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053153061 2000000000 42733692977581 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672376371/5000000000 : ℝ), (-557496861/2500000000 : ℝ), (1053153061/2000000000 : ℝ)] ![(8717097131487/20000000000000 : ℝ), (2736164269003/20000000000000 : ℝ), (42733692977581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672376371/5000000000 : ℝ)|^4169 ≤ (8717097131487/20000000000000 : ℝ)^3145
        have hw : |(2672376371/5000000000 : ℝ)|=(2672376371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557496861/2500000000 : ℝ)|^4169 ≤ (2736164269003/20000000000000 : ℝ)^3145
        have hw : |(-557496861/2500000000 : ℝ)|=(557496861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053153061/2000000000 : ℝ)|^4169 ≤ (42733692977581/100000000000000 : ℝ)^3145
        have hw : |(1053153061/2000000000 : ℝ)|=(1053153061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s7_2 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672376373/5000000000 : ℝ)*x 0 + (1316441327/2500000000 : ℝ)*x 1 + (-445997487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672376373/5000000000 : ℝ)^4169 ≤ (1743419428027/4000000000000 : ℝ)^3145 := by
    have hnat : (2672376373 : ℕ)^4169*4000000000000^3145 ≤ 1743419428027^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672376373 5000000000 1743419428027 4000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316441327/2500000000 : ℝ)^4169 ≤ (21366846504927/50000000000000 : ℝ)^3145 := by
    have hnat : (1316441327 : ℕ)^4169*50000000000000^3145 ≤ 21366846504927^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316441327 2500000000 21366846504927 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445997487/2000000000 : ℝ)^4169 ≤ (13680821271823/100000000000000 : ℝ)^3145 := by
    have hnat : (445997487 : ℕ)^4169*100000000000000^3145 ≤ 13680821271823^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445997487 2000000000 13680821271823 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672376373/5000000000 : ℝ), (1316441327/2500000000 : ℝ), (-445997487/2000000000 : ℝ)] ![(1743419428027/4000000000000 : ℝ), (21366846504927/50000000000000 : ℝ), (13680821271823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672376373/5000000000 : ℝ)|^4169 ≤ (1743419428027/4000000000000 : ℝ)^3145
        have hw : |(2672376373/5000000000 : ℝ)|=(2672376373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316441327/2500000000 : ℝ)|^4169 ≤ (21366846504927/50000000000000 : ℝ)^3145
        have hw : |(1316441327/2500000000 : ℝ)|=(1316441327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445997487/2000000000 : ℝ)|^4169 ≤ (13680821271823/100000000000000 : ℝ)^3145
        have hw : |(-445997487/2000000000 : ℝ)|=(445997487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s7_3 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2182124741/5000000000 : ℝ)*x 0 + (4239433831/10000000000 : ℝ)*x 1 + (2246359747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182124741/5000000000 : ℝ)^4169 ≤ (16658485034423/50000000000000 : ℝ)^3145 := by
    have hnat : (2182124741 : ℕ)^4169*50000000000000^3145 ≤ 16658485034423^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182124741 5000000000 16658485034423 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239433831/10000000000 : ℝ)^4169 ≤ (6411958731567/20000000000000 : ℝ)^3145 := by
    have hnat : (4239433831 : ℕ)^4169*20000000000000^3145 ≤ 6411958731567^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239433831 10000000000 6411958731567 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246359747/5000000000 : ℝ)^4169 ≤ (34623236255941/100000000000000 : ℝ)^3145 := by
    have hnat : (2246359747 : ℕ)^4169*100000000000000^3145 ≤ 34623236255941^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246359747 5000000000 34623236255941 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182124741/5000000000 : ℝ), (4239433831/10000000000 : ℝ), (2246359747/5000000000 : ℝ)] ![(16658485034423/50000000000000 : ℝ), (6411958731567/20000000000000 : ℝ), (34623236255941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182124741/5000000000 : ℝ)|^4169 ≤ (16658485034423/50000000000000 : ℝ)^3145
        have hw : |(2182124741/5000000000 : ℝ)|=(2182124741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239433831/10000000000 : ℝ)|^4169 ≤ (6411958731567/20000000000000 : ℝ)^3145
        have hw : |(4239433831/10000000000 : ℝ)|=(4239433831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246359747/5000000000 : ℝ)|^4169 ≤ (34623236255941/100000000000000 : ℝ)^3145
        have hw : |(2246359747/5000000000 : ℝ)|=(2246359747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s7_4 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082727703/5000000000 : ℝ)*x 0 + (1316521281/2500000000 : ℝ)*x 1 + (5392682361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082727703/5000000000 : ℝ)^4169 ≤ (13158506940467/100000000000000 : ℝ)^3145 := by
    have hnat : (1082727703 : ℕ)^4169*100000000000000^3145 ≤ 13158506940467^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082727703 5000000000 13158506940467 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316521281/2500000000 : ℝ)^4169 ≤ (21368566767171/50000000000000 : ℝ)^3145 := by
    have hnat : (1316521281 : ℕ)^4169*50000000000000^3145 ≤ 21368566767171^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316521281 2500000000 21368566767171 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392682361/10000000000 : ℝ)^4169 ≤ (44104359513853/100000000000000 : ℝ)^3145 := by
    have hnat : (5392682361 : ℕ)^4169*100000000000000^3145 ≤ 44104359513853^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392682361 10000000000 44104359513853 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082727703/5000000000 : ℝ), (1316521281/2500000000 : ℝ), (5392682361/10000000000 : ℝ)] ![(13158506940467/100000000000000 : ℝ), (21368566767171/50000000000000 : ℝ), (44104359513853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082727703/5000000000 : ℝ)|^4169 ≤ (13158506940467/100000000000000 : ℝ)^3145
        have hw : |(-1082727703/5000000000 : ℝ)|=(1082727703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316521281/2500000000 : ℝ)|^4169 ≤ (21368566767171/50000000000000 : ℝ)^3145
        have hw : |(1316521281/2500000000 : ℝ)|=(1316521281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392682361/10000000000 : ℝ)|^4169 ≤ (44104359513853/100000000000000 : ℝ)^3145
        have hw : |(5392682361/10000000000 : ℝ)|=(5392682361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s7_5 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656254627/5000000000 : ℝ)*x 0 + (-84122817/400000000 : ℝ)*x 1 + (53926823/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656254627/5000000000 : ℝ)^4169 ≤ (43237276479479/100000000000000 : ℝ)^3145 := by
    have hnat : (2656254627 : ℕ)^4169*100000000000000^3145 ≤ 43237276479479^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656254627 5000000000 43237276479479 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84122817/400000000 : ℝ)^4169 ≤ (12658364649829/100000000000000 : ℝ)^3145 := by
    have hnat : (84122817 : ℕ)^4169*100000000000000^3145 ≤ 12658364649829^3145*400000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84122817 400000000 12658364649829 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53926823/100000000 : ℝ)^4169 ≤ (11026089713131/25000000000000 : ℝ)^3145 := by
    have hnat : (53926823 : ℕ)^4169*25000000000000^3145 ≤ 11026089713131^3145*100000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53926823 100000000 11026089713131 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656254627/5000000000 : ℝ), (-84122817/400000000 : ℝ), (53926823/100000000 : ℝ)] ![(43237276479479/100000000000000 : ℝ), (12658364649829/100000000000000 : ℝ), (11026089713131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656254627/5000000000 : ℝ)|^4169 ≤ (43237276479479/100000000000000 : ℝ)^3145
        have hw : |(2656254627/5000000000 : ℝ)|=(2656254627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84122817/400000000 : ℝ)|^4169 ≤ (12658364649829/100000000000000 : ℝ)^3145
        have hw : |(-84122817/400000000 : ℝ)|=(84122817/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53926823/100000000 : ℝ)|^4169 ≤ (11026089713131/25000000000000 : ℝ)^3145
        have hw : |(53926823/100000000 : ℝ)|=(53926823/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s7_6 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664063647/1250000000 : ℝ)*x 0 + (134817059/250000000 : ℝ)*x 1 + (-131441903/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664063647/1250000000 : ℝ)^4169 ≤ (43237275637959/100000000000000 : ℝ)^3145 := by
    have hnat : (664063647 : ℕ)^4169*100000000000000^3145 ≤ 43237275637959^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664063647 1250000000 43237275637959 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134817059/250000000 : ℝ)^4169 ≤ (11026089875753/25000000000000 : ℝ)^3145 := by
    have hnat : (134817059 : ℕ)^4169*25000000000000^3145 ≤ 11026089875753^3145*250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134817059 250000000 11026089875753 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131441903/625000000 : ℝ)^4169 ≤ (632918241667/5000000000000 : ℝ)^3145 := by
    have hnat : (131441903 : ℕ)^4169*5000000000000^3145 ≤ 632918241667^3145*625000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131441903 625000000 632918241667 5000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664063647/1250000000 : ℝ), (134817059/250000000 : ℝ), (-131441903/625000000 : ℝ)] ![(43237275637959/100000000000000 : ℝ), (11026089875753/25000000000000 : ℝ), (632918241667/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664063647/1250000000 : ℝ)|^4169 ≤ (43237275637959/100000000000000 : ℝ)^3145
        have hw : |(664063647/1250000000 : ℝ)|=(664063647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134817059/250000000 : ℝ)|^4169 ≤ (11026089875753/25000000000000 : ℝ)^3145
        have hw : |(134817059/250000000 : ℝ)|=(134817059/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131441903/625000000 : ℝ)|^4169 ≤ (632918241667/5000000000000 : ℝ)^3145
        have hw : |(-131441903/625000000 : ℝ)|=(131441903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s7_7 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1091064831/2500000000 : ℝ)*x 0 + (449208279/1000000000 : ℝ)*x 1 + (4240072713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091064831/2500000000 : ℝ)^4169 ≤ (33317069666863/100000000000000 : ℝ)^3145 := by
    have hnat : (1091064831 : ℕ)^4169*100000000000000^3145 ≤ 33317069666863^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091064831 2500000000 33317069666863 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449208279/1000000000 : ℝ)^4169 ≤ (17308366003473/50000000000000 : ℝ)^3145 := by
    have hnat : (449208279 : ℕ)^4169*50000000000000^3145 ≤ 17308366003473^3145*1000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449208279 1000000000 17308366003473 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240072713/10000000000 : ℝ)^4169 ≤ (6413239661603/20000000000000 : ℝ)^3145 := by
    have hnat : (4240072713 : ℕ)^4169*20000000000000^3145 ≤ 6413239661603^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240072713 10000000000 6413239661603 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091064831/2500000000 : ℝ), (449208279/1000000000 : ℝ), (4240072713/10000000000 : ℝ)] ![(33317069666863/100000000000000 : ℝ), (17308366003473/50000000000000 : ℝ), (6413239661603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091064831/2500000000 : ℝ)|^4169 ≤ (33317069666863/100000000000000 : ℝ)^3145
        have hw : |(1091064831/2500000000 : ℝ)|=(1091064831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449208279/1000000000 : ℝ)|^4169 ≤ (17308366003473/50000000000000 : ℝ)^3145
        have hw : |(449208279/1000000000 : ℝ)|=(449208279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240072713/10000000000 : ℝ)|^4169 ≤ (6413239661603/20000000000000 : ℝ)^3145
        have hw : |(4240072713/10000000000 : ℝ)|=(4240072713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1145_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (2839/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3513/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (227/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (227/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (227/2000 : ℝ) ^ (8337/2048 : ℝ) ≤ (7112895351151701/50000000000000000000 : ℝ) := by
    have hpowers : (227/2000 : ℝ)^8337 ≤ (7112895351151701/50000000000000000000 : ℝ)^2048 := by
      have hnat : (227 : ℕ)^8337*50000000000000000000^2048 ≤ 7112895351151701^2048*2000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        227 2000 7112895351151701 50000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (227/2000 : ℝ)) (X := (7112895351151701/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7029/50000 : ℝ) ^ (8337/2048 : ℝ) ≤ (16995599214779781/50000000000000000000 : ℝ) := by
    have hpowers : (7029/50000 : ℝ)^8337 ≤ (16995599214779781/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7029 : ℕ)^8337*50000000000000000000^2048 ≤ 16995599214779781^2048*50000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7029 50000 16995599214779781 50000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7029/50000 : ℝ)) (X := (16995599214779781/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007112895351151701/25000000000000000000 : ℝ) ≤ (5000349421775293/5000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (25007112895351151701/25000000000000000000 : ℝ)^2048 ≤ (5000349421775293/5000000000000000 : ℝ)^8337 := by
      have hnat : (25007112895351151701 : ℕ)^2048*5000000000000000^8337 ≤ 5000349421775293^8337*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007112895351151701 25000000000000000000 5000349421775293 5000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000349421775293/5000000000000000 : ℝ)) (X := (25007112895351151701/25000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012054247282965741/25000000000000000000 : ℝ) ≤ (2500296061053817/2500000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (25012054247282965741/25000000000000000000 : ℝ)^2048 ≤ (2500296061053817/2500000000000000 : ℝ)^8337 := by
      have hnat : (25012054247282965741 : ℕ)^2048*2500000000000000^8337 ≤ 2500296061053817^8337*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012054247282965741 25000000000000000000 2500296061053817 2500000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500296061053817/2500000000000000 : ℝ)) (X := (25012054247282965741/25000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016995599214779781/25000000000000000000 : ℝ) ≤ (200033392897599/200000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (25016995599214779781/25000000000000000000 : ℝ)^2048 ≤ (200033392897599/200000000000000 : ℝ)^8337 := by
      have hnat : (25016995599214779781 : ℕ)^2048*200000000000000^8337 ≤ 200033392897599^8337*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016995599214779781 25000000000000000000 200033392897599 200000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200033392897599/200000000000000 : ℝ)) (X := (25016995599214779781/25000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7112895351151701/50000000000000000000 : ℝ) ≤ ((1691929617077919093/1692500000000000000 : ℝ)+2*(242700332341/135400000000000 : ℝ)*(227/2000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (1691929617077919093/1692500000000000000 : ℝ)+2*(242700332341/135400000000000 : ℝ)*(227/2000 : ℝ)=(5000349421775293/5000000000000000 : ℝ) by norm_num, show 1+2*(7112895351151701/50000000000000000000 : ℝ)=(25007112895351151701/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16995599214779781/50000000000000000000 : ℝ)+(7112895351151701/50000000000000000000 : ℝ) ≤ ((1691929617077919093/1692500000000000000 : ℝ)+(242700332341/135400000000000 : ℝ)*((7029/50000 : ℝ)+(227/2000 : ℝ)))^(8337/2048 : ℝ) := by
    rw [show (1691929617077919093/1692500000000000000 : ℝ)+(242700332341/135400000000000 : ℝ)*((7029/50000 : ℝ)+(227/2000 : ℝ))=(2500296061053817/2500000000000000 : ℝ) by norm_num, show 1+(16995599214779781/50000000000000000000 : ℝ)+(7112895351151701/50000000000000000000 : ℝ)=(25012054247282965741/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16995599214779781/50000000000000000000 : ℝ) ≤ ((1691929617077919093/1692500000000000000 : ℝ)+2*(242700332341/135400000000000 : ℝ)*(7029/50000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (1691929617077919093/1692500000000000000 : ℝ)+2*(242700332341/135400000000000 : ℝ)*(7029/50000 : ℝ)=(200033392897599/200000000000000 : ℝ) by norm_num, show 1+2*(16995599214779781/50000000000000000000 : ℝ)=(25016995599214779781/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1691929617077919093/1692500000000000000 : ℝ)*(X 1 0+X 2 0)+(242700332341/135400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (1691929617077919093/1692500000000000000 : ℝ)) (alpha := (242700332341/135400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1691929617077919093/1692500000000000000 : ℝ)*(X 0 1+X 2 1)+(242700332341/135400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (1691929617077919093/1692500000000000000 : ℝ)) (alpha := (242700332341/135400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1691929617077919093/1692500000000000000 : ℝ)*(X 0 2+X 1 2)+(242700332341/135400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (1691929617077919093/1692500000000000000 : ℝ)) (alpha := (242700332341/135400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2165450557/10000000000 : ℝ)*X 0 0+(2696501661/5000000000 : ℝ)*X 0 1+(1053153059/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672376371/5000000000 : ℝ)*X 1 0+(-557496861/2500000000 : ℝ)*X 1 1+(1053153061/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672376373/5000000000 : ℝ)*X 2 0+(1316441327/2500000000 : ℝ)*X 2 1+(-445997487/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182124741/5000000000 : ℝ)*X 0 0+(4239433831/10000000000 : ℝ)*X 0 1+(2246359747/5000000000 : ℝ)*X 0 2+(2182124741/5000000000 : ℝ)*X 1 0+(4239433831/10000000000 : ℝ)*X 1 1+(2246359747/5000000000 : ℝ)*X 1 2+(2182124741/5000000000 : ℝ)*X 2 0+(4239433831/10000000000 : ℝ)*X 2 1+(2246359747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1082727703/5000000000 : ℝ)*X 0 0+(1316521281/2500000000 : ℝ)*X 0 1+(5392682361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656254627/5000000000 : ℝ)*X 1 0+(-84122817/400000000 : ℝ)*X 1 1+(53926823/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664063647/1250000000 : ℝ)*X 2 0+(134817059/250000000 : ℝ)*X 2 1+(-131441903/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091064831/2500000000 : ℝ)*X 0 0+(449208279/1000000000 : ℝ)*X 0 1+(4240072713/10000000000 : ℝ)*X 0 2+(1091064831/2500000000 : ℝ)*X 1 0+(449208279/1000000000 : ℝ)*X 1 1+(4240072713/10000000000 : ℝ)*X 1 2+(1091064831/2500000000 : ℝ)*X 2 0+(449208279/1000000000 : ℝ)*X 2 1+(4240072713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34471504121279448914283/3385000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126328327/6250000000000 : ℝ)*(base19) + (950265293/50000000000000 : ℝ)*(base23) + (6766703/10000000000000 : ℝ)*(lower2) + (2493813/1000000000000 : ℝ)*(upper3) + (85732719/50000000000000 : ℝ)*(upper5) + (2951892034823737/50000000000000 : ℝ)*(major0) + (2951892034823737/50000000000000 : ℝ)*(major1) + (2951892034823737/50000000000000 : ℝ)*(major2) + (7859343551814159/100000000000000 : ℝ)*(sp0) + (1964849474260081/25000000000000 : ℝ)*(sp1) + (785939801776297/10000000000000 : ℝ)*(sp2) + (3948138393477443/100000000000000 : ℝ)*(sp3) + (56366479397/100000000000000 : ℝ)*(sp4) + (2948807043/10000000000000 : ℝ)*(sp7) + (123380246298371/3125000000000 : ℝ)*(f.failure) + (1964849979573389/25000000000000 : ℝ)*(f.sum) + (2124116601071/423125000000000000000000000 : ℝ)*base66 + (121176845687001959/84625000000000000000000000000000 : ℝ)*base68 + (357337045136123041/84625000000000000000000000000000 : ℝ)*base69 + (768802830763876959/84625000000000000000000000000000 : ℝ)*base72 + (795080353457/846250000000000000000000000 : ℝ)*base74 + (1061287518280373041/84625000000000000000000000000000 : ℝ)*base75 + (475096048920623041/84625000000000000000000000000000 : ℝ)*base77 + (1118500947201751959/84625000000000000000000000000000 : ℝ)*base80 + (26040873233253/3385000000000000000000000000 : ℝ)*base82 + (155421/62500000000000000000 : ℝ)*base90 + (155421/62500000000000000000 : ℝ)*base92 + (155421/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (856978374356303212595606613/84625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1836961741/100000000000000 : ℝ)*(base19) + (1006735379/50000000000000 : ℝ)*(base23) + (102424837/50000000000000 : ℝ)*(upper3) + (71183381/50000000000000 : ℝ)*(lower4) + (238644847/100000000000000 : ℝ)*(upper5) + (5933578052733151/100000000000000 : ℝ)*(major0) + (5933578052733151/100000000000000 : ℝ)*(major1) + (5933578052733151/100000000000000 : ℝ)*(major2) + (46748087371/100000000000000 : ℝ)*(sp1) + (50784895627/100000000000000 : ℝ)*(sp2) + (7899063098173467/100000000000000 : ℝ)*(sp4) + (1579802902624871/20000000000000 : ℝ)*(sp5) + (3949505149903541/50000000000000 : ℝ)*(sp6) + (1984046334866821/50000000000000 : ℝ)*(sp7) + (1984046334866821/50000000000000 : ℝ)*(f.failure) + (7899063098173467/100000000000000 : ℝ)*(f.sum) + (27869065337871/6770000000000000000000000000 : ℝ)*base65 + (743194426609089543/169250000000000000000000000000000 : ℝ)*base67 + (633926585142839543/169250000000000000000000000000000 : ℝ)*base69 + (2782681574148089543/169250000000000000000000000000000 : ℝ)*base71 + (16579269296879/6770000000000000000000000000 : ℝ)*base74 + (3440300766633839543/169250000000000000000000000000000 : ℝ)*base75 + (736732784199589543/169250000000000000000000000000000 : ℝ)*base77 + (2533558715395089543/169250000000000000000000000000000 : ℝ)*base79 + (35203543927559/6770000000000000000000000000 : ℝ)*base82 + (5971371/1000000000000000000000 : ℝ)*base90 + (5971371/1000000000000000000000 : ℝ)*base92 + (5971371/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1145_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1145_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1145_s8_0 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-216545489/1000000000 : ℝ)*x 0 + (1348235831/2500000000 : ℝ)*x 1 + (5265822517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216545489/1000000000 : ℝ)^4169 ≤ (6579251392029/50000000000000 : ℝ)^3145 := by
    have hnat : (216545489 : ℕ)^4169*50000000000000^3145 ≤ 6579251392029^3145*1000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216545489 1000000000 6579251392029 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348235831/2500000000 : ℝ)^4169 ≤ (5513398594633/12500000000000 : ℝ)^3145 := by
    have hnat : (1348235831 : ℕ)^4169*12500000000000^3145 ≤ 5513398594633^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348235831 2500000000 5513398594633 12500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265822517/10000000000 : ℝ)^4169 ≤ (8546861689851/20000000000000 : ℝ)^3145 := by
    have hnat : (5265822517 : ℕ)^4169*20000000000000^3145 ≤ 8546861689851^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265822517 10000000000 8546861689851 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216545489/1000000000 : ℝ), (1348235831/2500000000 : ℝ), (5265822517/10000000000 : ℝ)] ![(6579251392029/50000000000000 : ℝ), (5513398594633/12500000000000 : ℝ), (8546861689851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216545489/1000000000 : ℝ)|^4169 ≤ (6579251392029/50000000000000 : ℝ)^3145
        have hw : |(-216545489/1000000000 : ℝ)|=(216545489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348235831/2500000000 : ℝ)|^4169 ≤ (5513398594633/12500000000000 : ℝ)^3145
        have hw : |(1348235831/2500000000 : ℝ)|=(1348235831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265822517/10000000000 : ℝ)|^4169 ≤ (8546861689851/20000000000000 : ℝ)^3145
        have hw : |(5265822517/10000000000 : ℝ)|=(5265822517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s8_1 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668092237/1250000000 : ℝ)*x 0 + (-445986297/2000000000 : ℝ)*x 1 + (5265822527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668092237/1250000000 : ℝ)^4169 ≤ (43585325172313/100000000000000 : ℝ)^3145 := by
    have hnat : (668092237 : ℕ)^4169*100000000000000^3145 ≤ 43585325172313^3145*1250000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668092237 1250000000 43585325172313 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445986297/2000000000 : ℝ)^4169 ≤ (13680366263527/100000000000000 : ℝ)^3145 := by
    have hnat : (445986297 : ℕ)^4169*100000000000000^3145 ≤ 13680366263527^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445986297 2000000000 13680366263527 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265822527/10000000000 : ℝ)^4169 ≤ (1335447142401/3125000000000 : ℝ)^3145 := by
    have hnat : (5265822527 : ℕ)^4169*3125000000000^3145 ≤ 1335447142401^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265822527 10000000000 1335447142401 3125000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668092237/1250000000 : ℝ), (-445986297/2000000000 : ℝ), (5265822527/10000000000 : ℝ)] ![(43585325172313/100000000000000 : ℝ), (13680366263527/100000000000000 : ℝ), (1335447142401/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668092237/1250000000 : ℝ)|^4169 ≤ (43585325172313/100000000000000 : ℝ)^3145
        have hw : |(668092237/1250000000 : ℝ)|=(668092237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445986297/2000000000 : ℝ)|^4169 ≤ (13680366263527/100000000000000 : ℝ)^3145
        have hw : |(-445986297/2000000000 : ℝ)|=(445986297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265822527/10000000000 : ℝ)|^4169 ≤ (1335447142401/3125000000000 : ℝ)^3145
        have hw : |(5265822527/10000000000 : ℝ)|=(5265822527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s8_2 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334046123/625000000 : ℝ)*x 0 + (5265822469/10000000000 : ℝ)*x 1 + (-1114965733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334046123/625000000 : ℝ)^4169 ≤ (5448165743829/12500000000000 : ℝ)^3145 := by
    have hnat : (334046123 : ℕ)^4169*12500000000000^3145 ≤ 5448165743829^3145*625000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334046123 625000000 5448165743829 12500000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265822469/10000000000 : ℝ)^4169 ≤ (21367153966441/50000000000000 : ℝ)^3145 := by
    have hnat : (5265822469 : ℕ)^4169*50000000000000^3145 ≤ 21367153966441^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265822469 10000000000 21367153966441 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114965733/5000000000 : ℝ)^4169 ≤ (3420091527253/25000000000000 : ℝ)^3145 := by
    have hnat : (1114965733 : ℕ)^4169*25000000000000^3145 ≤ 3420091527253^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114965733 5000000000 3420091527253 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334046123/625000000 : ℝ), (5265822469/10000000000 : ℝ), (-1114965733/5000000000 : ℝ)] ![(5448165743829/12500000000000 : ℝ), (21367153966441/50000000000000 : ℝ), (3420091527253/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334046123/625000000 : ℝ)|^4169 ≤ (5448165743829/12500000000000 : ℝ)^3145
        have hw : |(334046123/625000000 : ℝ)|=(334046123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265822469/10000000000 : ℝ)|^4169 ≤ (21367153966441/50000000000000 : ℝ)^3145
        have hw : |(5265822469/10000000000 : ℝ)|=(5265822469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1114965733/5000000000 : ℝ)|^4169 ≤ (3420091527253/25000000000000 : ℝ)^3145
        have hw : |(-1114965733/5000000000 : ℝ)|=(1114965733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s8_3 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364252429/10000000000 : ℝ)*x 0 + (169582001/400000000 : ℝ)*x 1 + (898520511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364252429/10000000000 : ℝ)^4169 ≤ (33316999891573/100000000000000 : ℝ)^3145 := by
    have hnat : (4364252429 : ℕ)^4169*100000000000000^3145 ≤ 33316999891573^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364252429 10000000000 33316999891573 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169582001/400000000 : ℝ)^4169 ≤ (6412191690701/20000000000000 : ℝ)^3145 := by
    have hnat : (169582001 : ℕ)^4169*20000000000000^3145 ≤ 6412191690701^3145*400000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169582001 400000000 6412191690701 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898520511/2000000000 : ℝ)^4169 ≤ (17311020821609/50000000000000 : ℝ)^3145 := by
    have hnat : (898520511 : ℕ)^4169*50000000000000^3145 ≤ 17311020821609^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898520511 2000000000 17311020821609 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364252429/10000000000 : ℝ), (169582001/400000000 : ℝ), (898520511/2000000000 : ℝ)] ![(33316999891573/100000000000000 : ℝ), (6412191690701/20000000000000 : ℝ), (17311020821609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364252429/10000000000 : ℝ)|^4169 ≤ (33316999891573/100000000000000 : ℝ)^3145
        have hw : |(4364252429/10000000000 : ℝ)|=(4364252429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169582001/400000000 : ℝ)|^4169 ≤ (6412191690701/20000000000000 : ℝ)^3145
        have hw : |(169582001/400000000 : ℝ)|=(169582001/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898520511/2000000000 : ℝ)|^4169 ≤ (17311020821609/50000000000000 : ℝ)^3145
        have hw : |(898520511/2000000000 : ℝ)|=(898520511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s8_4 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-541364937/2500000000 : ℝ)*x 0 + (5266141653/10000000000 : ℝ)*x 1 + (5392623041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541364937/2500000000 : ℝ)^4169 ≤ (822408869721/6250000000000 : ℝ)^3145 := by
    have hnat : (541364937 : ℕ)^4169*6250000000000^3145 ≤ 822408869721^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541364937 2500000000 822408869721 6250000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266141653/10000000000 : ℝ)^4169 ≤ (8547548334099/20000000000000 : ℝ)^3145 := by
    have hnat : (5266141653 : ℕ)^4169*20000000000000^3145 ≤ 8547548334099^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266141653 10000000000 8547548334099 20000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392623041/10000000000 : ℝ)^4169 ≤ (44103716399371/100000000000000 : ℝ)^3145 := by
    have hnat : (5392623041 : ℕ)^4169*100000000000000^3145 ≤ 44103716399371^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392623041 10000000000 44103716399371 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-541364937/2500000000 : ℝ), (5266141653/10000000000 : ℝ), (5392623041/10000000000 : ℝ)] ![(822408869721/6250000000000 : ℝ), (8547548334099/20000000000000 : ℝ), (44103716399371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-541364937/2500000000 : ℝ)|^4169 ≤ (822408869721/6250000000000 : ℝ)^3145
        have hw : |(-541364937/2500000000 : ℝ)|=(541364937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266141653/10000000000 : ℝ)|^4169 ≤ (8547548334099/20000000000000 : ℝ)^3145
        have hw : |(5266141653/10000000000 : ℝ)|=(5266141653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392623041/10000000000 : ℝ)|^4169 ≤ (44103716399371/100000000000000 : ℝ)^3145
        have hw : |(5392623041/10000000000 : ℝ)|=(5392623041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s8_5 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656262131/5000000000 : ℝ)*x 0 + (-1051565291/5000000000 : ℝ)*x 1 + (5392623093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656262131/5000000000 : ℝ)^4169 ≤ (21618719198323/50000000000000 : ℝ)^3145 := by
    have hnat : (2656262131 : ℕ)^4169*50000000000000^3145 ≤ 21618719198323^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656262131 5000000000 21618719198323 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051565291/5000000000 : ℝ)^4169 ≤ (79117778937/625000000000 : ℝ)^3145 := by
    have hnat : (1051565291 : ℕ)^4169*625000000000^3145 ≤ 79117778937^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051565291 5000000000 79117778937 625000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392623093/10000000000 : ℝ)^4169 ≤ (70565947141/160000000000 : ℝ)^3145 := by
    have hnat : (5392623093 : ℕ)^4169*160000000000^3145 ≤ 70565947141^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392623093 10000000000 70565947141 160000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656262131/5000000000 : ℝ), (-1051565291/5000000000 : ℝ), (5392623093/10000000000 : ℝ)] ![(21618719198323/50000000000000 : ℝ), (79117778937/625000000000 : ℝ), (70565947141/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656262131/5000000000 : ℝ)|^4169 ≤ (21618719198323/50000000000000 : ℝ)^3145
        have hw : |(2656262131/5000000000 : ℝ)|=(2656262131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1051565291/5000000000 : ℝ)|^4169 ≤ (79117778937/625000000000 : ℝ)^3145
        have hw : |(-1051565291/5000000000 : ℝ)|=(1051565291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392623093/10000000000 : ℝ)|^4169 ≤ (70565947141/160000000000 : ℝ)^3145
        have hw : |(5392623093/10000000000 : ℝ)|=(5392623093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s8_6 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328130909/2500000000 : ℝ)*x 0 + (2696311529/5000000000 : ℝ)*x 1 + (-525782869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328130909/2500000000 : ℝ)^4169 ≤ (21618715821451/50000000000000 : ℝ)^3145 := by
    have hnat : (1328130909 : ℕ)^4169*50000000000000^3145 ≤ 21618715821451^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328130909 2500000000 21618715821451 50000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696311529/5000000000 : ℝ)^4169 ≤ (11025929145919/25000000000000 : ℝ)^3145 := by
    have hnat : (2696311529 : ℕ)^4169*25000000000000^3145 ≤ 11025929145919^3145*5000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696311529 5000000000 11025929145919 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525782869/2500000000 : ℝ)^4169 ≤ (791178235187/6250000000000 : ℝ)^3145 := by
    have hnat : (525782869 : ℕ)^4169*6250000000000^3145 ≤ 791178235187^3145*2500000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525782869 2500000000 791178235187 6250000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328130909/2500000000 : ℝ), (2696311529/5000000000 : ℝ), (-525782869/2500000000 : ℝ)] ![(21618715821451/50000000000000 : ℝ), (11025929145919/25000000000000 : ℝ), (791178235187/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328130909/2500000000 : ℝ)|^4169 ≤ (21618715821451/50000000000000 : ℝ)^3145
        have hw : |(1328130909/2500000000 : ℝ)|=(1328130909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696311529/5000000000 : ℝ)|^4169 ≤ (11025929145919/25000000000000 : ℝ)^3145
        have hw : |(2696311529/5000000000 : ℝ)|=(2696311529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525782869/2500000000 : ℝ)|^4169 ≤ (791178235187/6250000000000 : ℝ)^3145
        have hw : |(-525782869/2500000000 : ℝ)|=(525782869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1145_s8_7 (p : ℝ) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872852329/2000000000 : ℝ)*x 0 + (4491967067/10000000000 : ℝ)*x 1 + (33126471/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872852329/2000000000 : ℝ)^4169 ≤ (33317093154681/100000000000000 : ℝ)^3145 := by
    have hnat : (872852329 : ℕ)^4169*100000000000000^3145 ≤ 33317093154681^3145*2000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872852329 2000000000 33317093154681 100000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491967067/10000000000 : ℝ)^4169 ≤ (8653887467751/25000000000000 : ℝ)^3145 := by
    have hnat : (4491967067 : ℕ)^4169*25000000000000^3145 ≤ 8653887467751^3145*10000000000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491967067 10000000000 8653887467751 25000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33126471/78125000 : ℝ)^4169 ≤ (3206735695529/10000000000000 : ℝ)^3145 := by
    have hnat : (33126471 : ℕ)^4169*10000000000000^3145 ≤ 3206735695529^3145*78125000^4169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33126471 78125000 3206735695529 10000000000000 4169 3145 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4169/1024 : ℝ)) 4169 3145 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872852329/2000000000 : ℝ), (4491967067/10000000000 : ℝ), (33126471/78125000 : ℝ)] ![(33317093154681/100000000000000 : ℝ), (8653887467751/25000000000000 : ℝ), (3206735695529/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872852329/2000000000 : ℝ)|^4169 ≤ (33317093154681/100000000000000 : ℝ)^3145
        have hw : |(872852329/2000000000 : ℝ)|=(872852329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491967067/10000000000 : ℝ)|^4169 ≤ (8653887467751/25000000000000 : ℝ)^3145
        have hw : |(4491967067/10000000000 : ℝ)|=(4491967067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33126471/78125000 : ℝ)|^4169 ≤ (3206735695529/10000000000000 : ℝ)^3145
        have hw : |(33126471/78125000 : ℝ)|=(33126471/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1145_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5679/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (281/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2839/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2839/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2839/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2839/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2839/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2839/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2839/25000 : ℝ) ^ (8337/2048 : ℝ) ≤ (14256428965331393/100000000000000000000 : ℝ) := by
    have hpowers : (2839/25000 : ℝ)^8337 ≤ (14256428965331393/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2839 : ℕ)^8337*100000000000000000000^2048 ≤ 14256428965331393^2048*25000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2839 25000 14256428965331393 100000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2839/25000 : ℝ)) (X := (14256428965331393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3513/25000 : ℝ) ^ (8337/2048 : ℝ) ≤ (16966089879069501/50000000000000000000 : ℝ) := by
    have hpowers : (3513/25000 : ℝ)^8337 ≤ (16966089879069501/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3513 : ℕ)^8337*50000000000000000000^2048 ≤ 16966089879069501^2048*25000^8337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3513 25000 16966089879069501 50000000000000000000 8337 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3513/25000 : ℝ)) (X := (16966089879069501/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014256428965331393/50000000000000000000 : ℝ) ≤ (5000350174248419/5000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (50014256428965331393/50000000000000000000 : ℝ)^2048 ≤ (5000350174248419/5000000000000000 : ℝ)^8337 := by
      have hnat : (50014256428965331393 : ℕ)^2048*5000000000000000^8337 ≤ 5000350174248419^8337*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014256428965331393 50000000000000000000 5000350174248419 5000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000350174248419/5000000000000000 : ℝ)) (X := (50014256428965331393/50000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009637721744694079/20000000000000000000 : ℝ) ≤ (5000591773649251/5000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (20009637721744694079/20000000000000000000 : ℝ)^2048 ≤ (5000591773649251/5000000000000000 : ℝ)^8337 := by
      have hnat : (20009637721744694079 : ℕ)^2048*5000000000000000^8337 ≤ 5000591773649251^8337*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009637721744694079 20000000000000000000 5000591773649251 5000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000591773649251/5000000000000000 : ℝ)) (X := (20009637721744694079/20000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016966089879069501/25000000000000000000 : ℝ) ≤ (5000833373050083/5000000000000000 : ℝ) ^ (8337/2048 : ℝ) := by
    have hpowers : (25016966089879069501/25000000000000000000 : ℝ)^2048 ≤ (5000833373050083/5000000000000000 : ℝ)^8337 := by
      have hnat : (25016966089879069501 : ℕ)^2048*5000000000000000^8337 ≤ 5000833373050083^8337*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016966089879069501 25000000000000000000 5000833373050083 5000000000000000 2048 8337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000833373050083/5000000000000000 : ℝ)) (X := (25016966089879069501/25000000000000000000 : ℝ)) (by norm_num) 8337 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14256428965331393/100000000000000000000 : ℝ) ≤ ((336886421604551031/337000000000000000 : ℝ)+2*(1887495319/1053125000000 : ℝ)*(2839/25000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (336886421604551031/337000000000000000 : ℝ)+2*(1887495319/1053125000000 : ℝ)*(2839/25000 : ℝ)=(5000350174248419/5000000000000000 : ℝ) by norm_num, show 1+2*(14256428965331393/100000000000000000000 : ℝ)=(50014256428965331393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16966089879069501/50000000000000000000 : ℝ)+(14256428965331393/100000000000000000000 : ℝ) ≤ ((336886421604551031/337000000000000000 : ℝ)+(1887495319/1053125000000 : ℝ)*((3513/25000 : ℝ)+(2839/25000 : ℝ)))^(8337/2048 : ℝ) := by
    rw [show (336886421604551031/337000000000000000 : ℝ)+(1887495319/1053125000000 : ℝ)*((3513/25000 : ℝ)+(2839/25000 : ℝ))=(5000591773649251/5000000000000000 : ℝ) by norm_num, show 1+(16966089879069501/50000000000000000000 : ℝ)+(14256428965331393/100000000000000000000 : ℝ)=(20009637721744694079/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16966089879069501/50000000000000000000 : ℝ) ≤ ((336886421604551031/337000000000000000 : ℝ)+2*(1887495319/1053125000000 : ℝ)*(3513/25000 : ℝ))^(8337/2048 : ℝ) := by
    rw [show (336886421604551031/337000000000000000 : ℝ)+2*(1887495319/1053125000000 : ℝ)*(3513/25000 : ℝ)=(5000833373050083/5000000000000000 : ℝ) by norm_num, show 1+2*(16966089879069501/50000000000000000000 : ℝ)=(25016966089879069501/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (336886421604551031/337000000000000000 : ℝ)*(X 1 0+X 2 0)+(1887495319/1053125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2839/25000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (336886421604551031/337000000000000000 : ℝ)) (alpha := (1887495319/1053125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (336886421604551031/337000000000000000 : ℝ)*(X 0 1+X 2 1)+(1887495319/1053125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2839/25000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (336886421604551031/337000000000000000 : ℝ)) (alpha := (1887495319/1053125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (336886421604551031/337000000000000000 : ℝ)*(X 0 2+X 1 2)+(1887495319/1053125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8337/2048 : ℝ)) (lo := (2839/25000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (336886421604551031/337000000000000000 : ℝ)) (alpha := (1887495319/1053125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-216545489/1000000000 : ℝ)*X 0 0+(1348235831/2500000000 : ℝ)*X 0 1+(5265822517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668092237/1250000000 : ℝ)*X 1 0+(-445986297/2000000000 : ℝ)*X 1 1+(5265822527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334046123/625000000 : ℝ)*X 2 0+(5265822469/10000000000 : ℝ)*X 2 1+(-1114965733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364252429/10000000000 : ℝ)*X 0 0+(169582001/400000000 : ℝ)*X 0 1+(898520511/2000000000 : ℝ)*X 0 2+(4364252429/10000000000 : ℝ)*X 1 0+(169582001/400000000 : ℝ)*X 1 1+(898520511/2000000000 : ℝ)*X 1 2+(4364252429/10000000000 : ℝ)*X 2 0+(169582001/400000000 : ℝ)*X 2 1+(898520511/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-541364937/2500000000 : ℝ)*X 0 0+(5266141653/10000000000 : ℝ)*X 0 1+(5392623041/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656262131/5000000000 : ℝ)*X 1 0+(-1051565291/5000000000 : ℝ)*X 1 1+(5392623093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328130909/2500000000 : ℝ)*X 2 0+(2696311529/5000000000 : ℝ)*X 2 1+(-525782869/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872852329/2000000000 : ℝ)*X 0 0+(4491967067/10000000000 : ℝ)*X 0 1+(33126471/78125000 : ℝ)*X 0 2+(872852329/2000000000 : ℝ)*X 1 0+(4491967067/10000000000 : ℝ)*X 1 1+(33126471/78125000 : ℝ)*X 1 2+(872852329/2000000000 : ℝ)*X 2 0+(4491967067/10000000000 : ℝ)*X 2 1+(33126471/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1145_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46167713759724865430791251/16850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140262073/25000000000000 : ℝ)*(base19) + (664754343/100000000000000 : ℝ)*(base23) + (605557/50000000000000 : ℝ)*(lower2) + (1549069/5000000000000 : ℝ)*(upper3) + (79475757/100000000000000 : ℝ)*(upper5) + (5909167936062793/100000000000000 : ℝ)*(major0) + (5909167936062793/100000000000000 : ℝ)*(major1) + (5909167936062793/100000000000000 : ℝ)*(major2) + (3933274151607067/50000000000000 : ℝ)*(sp0) + (7866566866330291/100000000000000 : ℝ)*(sp1) + (98332084532803/1250000000000 : ℝ)*(sp2) + (395175869556773/10000000000000 : ℝ)*(sp3) + (19124164449/100000000000000 : ℝ)*(sp4) + (60361553/625000000000 : ℝ)*(sp7) + (395176835341621/10000000000000 : ℝ)*(f.failure) + (7866567427378583/100000000000000 : ℝ)*(f.sum) + (2528391283607/842500000000000000000000000 : ℝ)*base65 + (221569580023229583/33700000000000000000000000000000 : ℝ)*base67 + (69077419796570417/33700000000000000000000000000000 : ℝ)*base70 + (25943220546129583/33700000000000000000000000000000 : ℝ)*base71 + (3381829182569/1685000000000000000000000000 : ℝ)*base73 + (391603579624429583/33700000000000000000000000000000 : ℝ)*base75 + (179112402334670417/33700000000000000000000000000000 : ℝ)*base78 + (322750023709329583/33700000000000000000000000000000 : ℝ)*base79 + (500619387903/842500000000000000000000000 : ℝ)*base82 + (13829/200000000000000000000 : ℝ)*base89 + (13829/200000000000000000000 : ℝ)*base91 + (13829/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38483990976628157154088371/8425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164664513/50000000000000 : ℝ)*(base19) + (25508487/20000000000000 : ℝ)*(upper1) + (307021867/100000000000000 : ℝ)*(upper2) + (140804443/100000000000000 : ℝ)*(lower4) + (9187919/100000000000000 : ℝ)*(lower5) + (5939024808121047/100000000000000 : ℝ)*(major0) + (5939024808121047/100000000000000 : ℝ)*(major1) + (5939024808121047/100000000000000 : ℝ)*(major2) + (3605077237/25000000000000 : ℝ)*(sp0) + (7937501417/20000000000000 : ℝ)*(sp1) + (7906299844938789/100000000000000 : ℝ)*(sp4) + (3953137124205813/50000000000000 : ℝ)*(sp5) + (7906314265247737/100000000000000 : ℝ)*(sp6) + (794347039746651/20000000000000 : ℝ)*(sp7) + (794347039746651/20000000000000 : ℝ)*(f.failure) + (7906314265247737/100000000000000 : ℝ)*(f.sum) + (2416526790421/1685000000000000000000000000 : ℝ)*base65 + (637264490685390543/33700000000000000000000000000000 : ℝ)*base68 + (457093589284090543/33700000000000000000000000000000 : ℝ)*base70 + (555869325289490543/33700000000000000000000000000000 : ℝ)*base72 + (643411229613/210625000000000000000000000 : ℝ)*base74 + (805260540851690543/33700000000000000000000000000000 : ℝ)*base76 + (11903268238509457/33700000000000000000000000000000 : ℝ)*base77 + (485822701990290543/33700000000000000000000000000000 : ℝ)*base80 + (543950218649/421250000000000000000000000 : ℝ)*base81 + (3052299/400000000000000000000 : ℝ)*base89 + (3052299/400000000000000000000 : ℝ)*base91 + (3052299/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1145_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1145_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1145_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1145_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1145_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1145_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1145_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
