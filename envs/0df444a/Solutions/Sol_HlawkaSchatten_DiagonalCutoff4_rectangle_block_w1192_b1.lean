-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1192_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:00:04.063887+00:00
-- url     : https://prove2.me/submissions/43adadd1-0921-4bb6-92ce-939d4fc00865

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
theorem support_rectangle_w1192_s3_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267489011/1250000000 : ℝ)*x 0 + (2712110189/5000000000 : ℝ)*x 1 + (5236570039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267489011/1250000000 : ℝ)^8385 ≤ (13001468498389/100000000000000 : ℝ)^6337 := by
    have hnat : (267489011 : ℕ)^8385*100000000000000^6337 ≤ 13001468498389^6337*1250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267489011 1250000000 13001468498389 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712110189/5000000000 : ℝ)^8385 ≤ (11128076998213/25000000000000 : ℝ)^6337 := by
    have hnat : (2712110189 : ℕ)^8385*25000000000000^6337 ≤ 11128076998213^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712110189 5000000000 11128076998213 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236570039/10000000000 : ℝ)^8385 ≤ (10621555873483/25000000000000 : ℝ)^6337 := by
    have hnat : (5236570039 : ℕ)^8385*25000000000000^6337 ≤ 10621555873483^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236570039 10000000000 10621555873483 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267489011/1250000000 : ℝ), (2712110189/5000000000 : ℝ), (5236570039/10000000000 : ℝ)] ![(13001468498389/100000000000000 : ℝ), (11128076998213/25000000000000 : ℝ), (10621555873483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267489011/1250000000 : ℝ)|^8385 ≤ (13001468498389/100000000000000 : ℝ)^6337
        have hw : |(-267489011/1250000000 : ℝ)|=(267489011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712110189/5000000000 : ℝ)|^8385 ≤ (11128076998213/25000000000000 : ℝ)^6337
        have hw : |(2712110189/5000000000 : ℝ)|=(2712110189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236570039/10000000000 : ℝ)|^8385 ≤ (10621555873483/25000000000000 : ℝ)^6337
        have hw : |(5236570039/10000000000 : ℝ)|=(5236570039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s3_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (214104643/400000000 : ℝ)*x 0 + (-447146313/2000000000 : ℝ)*x 1 + (5236570261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214104643/400000000 : ℝ)^8385 ≤ (874729398297/2000000000000 : ℝ)^6337 := by
    have hnat : (214104643 : ℕ)^8385*2000000000000^6337 ≤ 874729398297^6337*400000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214104643 400000000 874729398297 2000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447146313/2000000000 : ℝ)^8385 ≤ (13777304192241/100000000000000 : ℝ)^6337 := by
    have hnat : (447146313 : ℕ)^8385*100000000000000^6337 ≤ 13777304192241^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447146313 2000000000 13777304192241 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236570261/10000000000 : ℝ)^8385 ≤ (10621556469301/25000000000000 : ℝ)^6337 := by
    have hnat : (5236570261 : ℕ)^8385*25000000000000^6337 ≤ 10621556469301^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236570261 10000000000 10621556469301 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214104643/400000000 : ℝ), (-447146313/2000000000 : ℝ), (5236570261/10000000000 : ℝ)] ![(874729398297/2000000000000 : ℝ), (13777304192241/100000000000000 : ℝ), (10621556469301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214104643/400000000 : ℝ)|^8385 ≤ (874729398297/2000000000000 : ℝ)^6337
        have hw : |(214104643/400000000 : ℝ)|=(214104643/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447146313/2000000000 : ℝ)|^8385 ≤ (13777304192241/100000000000000 : ℝ)^6337
        have hw : |(-447146313/2000000000 : ℝ)|=(447146313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236570261/10000000000 : ℝ)|^8385 ≤ (10621556469301/25000000000000 : ℝ)^6337
        have hw : |(5236570261/10000000000 : ℝ)|=(5236570261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s3_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352615953/10000000000 : ℝ)*x 0 + (2618285247/5000000000 : ℝ)*x 1 + (-111786571/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352615953/10000000000 : ℝ)^8385 ≤ (43736468595813/100000000000000 : ℝ)^6337 := by
    have hnat : (5352615953 : ℕ)^8385*100000000000000^6337 ≤ 43736468595813^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352615953 10000000000 43736468595813 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618285247/5000000000 : ℝ)^8385 ≤ (21243114189283/50000000000000 : ℝ)^6337 := by
    have hnat : (2618285247 : ℕ)^8385*50000000000000^6337 ≤ 21243114189283^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618285247 5000000000 21243114189283 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111786571/500000000 : ℝ)^8385 ≤ (1377730300993/10000000000000 : ℝ)^6337 := by
    have hnat : (111786571 : ℕ)^8385*10000000000000^6337 ≤ 1377730300993^6337*500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111786571 500000000 1377730300993 10000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352615953/10000000000 : ℝ), (2618285247/5000000000 : ℝ), (-111786571/500000000 : ℝ)] ![(43736468595813/100000000000000 : ℝ), (21243114189283/50000000000000 : ℝ), (1377730300993/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352615953/10000000000 : ℝ)|^8385 ≤ (43736468595813/100000000000000 : ℝ)^6337
        have hw : |(5352615953/10000000000 : ℝ)|=(5352615953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618285247/5000000000 : ℝ)|^8385 ≤ (21243114189283/50000000000000 : ℝ)^6337
        have hw : |(2618285247/5000000000 : ℝ)|=(2618285247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111786571/500000000 : ℝ)|^8385 ≤ (1377730300993/10000000000000 : ℝ)^6337
        have hw : |(-111786571/500000000 : ℝ)|=(111786571/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s3_3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177859127/5000000000 : ℝ)*x 0 + (4171230301/10000000000 : ℝ)*x 1 + (4548219971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177859127/5000000000 : ℝ)^8385 ≤ (16648712320563/50000000000000 : ℝ)^6337 := by
    have hnat : (2177859127 : ℕ)^8385*50000000000000^6337 ≤ 16648712320563^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177859127 5000000000 16648712320563 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171230301/10000000000 : ℝ)^8385 ≤ (6288841346873/20000000000000 : ℝ)^6337 := by
    have hnat : (4171230301 : ℕ)^8385*20000000000000^6337 ≤ 6288841346873^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171230301 10000000000 6288841346873 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4548219971/10000000000 : ℝ)^8385 ≤ (17629184306019/50000000000000 : ℝ)^6337 := by
    have hnat : (4548219971 : ℕ)^8385*50000000000000^6337 ≤ 17629184306019^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548219971 10000000000 17629184306019 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177859127/5000000000 : ℝ), (4171230301/10000000000 : ℝ), (4548219971/10000000000 : ℝ)] ![(16648712320563/50000000000000 : ℝ), (6288841346873/20000000000000 : ℝ), (17629184306019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177859127/5000000000 : ℝ)|^8385 ≤ (16648712320563/50000000000000 : ℝ)^6337
        have hw : |(2177859127/5000000000 : ℝ)|=(2177859127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171230301/10000000000 : ℝ)|^8385 ≤ (6288841346873/20000000000000 : ℝ)^6337
        have hw : |(4171230301/10000000000 : ℝ)|=(4171230301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4548219971/10000000000 : ℝ)|^8385 ≤ (17629184306019/50000000000000 : ℝ)^6337
        have hw : |(4548219971/10000000000 : ℝ)|=(4548219971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s3_4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139928083/10000000000 : ℝ)*x 0 + (5237274163/10000000000 : ℝ)*x 1 + (5423512347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139928083/10000000000 : ℝ)^8385 ≤ (13001597086437/100000000000000 : ℝ)^6337 := by
    have hnat : (2139928083 : ℕ)^8385*100000000000000^6337 ≤ 13001597086437^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139928083 10000000000 13001597086437 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237274163/10000000000 : ℝ)^8385 ≤ (42493782751719/100000000000000 : ℝ)^6337 := by
    have hnat : (5237274163 : ℕ)^8385*100000000000000^6337 ≤ 42493782751719^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237274163 10000000000 42493782751719 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423512347/10000000000 : ℝ)^8385 ≤ (4450462013651/10000000000000 : ℝ)^6337 := by
    have hnat : (5423512347 : ℕ)^8385*10000000000000^6337 ≤ 4450462013651^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423512347 10000000000 4450462013651 10000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139928083/10000000000 : ℝ), (5237274163/10000000000 : ℝ), (5423512347/10000000000 : ℝ)] ![(13001597086437/100000000000000 : ℝ), (42493782751719/100000000000000 : ℝ), (4450462013651/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139928083/10000000000 : ℝ)|^8385 ≤ (13001597086437/100000000000000 : ℝ)^6337
        have hw : |(-2139928083/10000000000 : ℝ)|=(2139928083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237274163/10000000000 : ℝ)|^8385 ≤ (42493782751719/100000000000000 : ℝ)^6337
        have hw : |(5237274163/10000000000 : ℝ)|=(5237274163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423512347/10000000000 : ℝ)|^8385 ≤ (4450462013651/10000000000000 : ℝ)^6337
        have hw : |(5423512347/10000000000 : ℝ)|=(5423512347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s3_5 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304905943/10000000000 : ℝ)*x 0 + (-409757817/2000000000 : ℝ)*x 1 + (5423512279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304905943/10000000000 : ℝ)^8385 ≤ (43221383174653/100000000000000 : ℝ)^6337 := by
    have hnat : (5304905943 : ℕ)^8385*100000000000000^6337 ≤ 43221383174653^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304905943 10000000000 43221383174653 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409757817/2000000000 : ℝ)^8385 ≤ (3068499353461/25000000000000 : ℝ)^6337 := by
    have hnat : (409757817 : ℕ)^8385*25000000000000^6337 ≤ 3068499353461^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409757817 2000000000 3068499353461 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423512279/10000000000 : ℝ)^8385 ≤ (1390769356193/3125000000000 : ℝ)^6337 := by
    have hnat : (5423512279 : ℕ)^8385*3125000000000^6337 ≤ 1390769356193^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423512279 10000000000 1390769356193 3125000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304905943/10000000000 : ℝ), (-409757817/2000000000 : ℝ), (5423512279/10000000000 : ℝ)] ![(43221383174653/100000000000000 : ℝ), (3068499353461/25000000000000 : ℝ), (1390769356193/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304905943/10000000000 : ℝ)|^8385 ≤ (43221383174653/100000000000000 : ℝ)^6337
        have hw : |(5304905943/10000000000 : ℝ)|=(5304905943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409757817/2000000000 : ℝ)|^8385 ≤ (3068499353461/25000000000000 : ℝ)^6337
        have hw : |(-409757817/2000000000 : ℝ)|=(409757817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423512279/10000000000 : ℝ)|^8385 ≤ (1390769356193/3125000000000 : ℝ)^6337
        have hw : |(5423512279/10000000000 : ℝ)|=(5423512279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s3_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304905573/10000000000 : ℝ)*x 0 + (135587817/250000000 : ℝ)*x 1 + (-2048789039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304905573/10000000000 : ℝ)^8385 ≤ (8644275837171/20000000000000 : ℝ)^6337 := by
    have hnat : (5304905573 : ℕ)^8385*20000000000000^6337 ≤ 8644275837171^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304905573 10000000000 8644275837171 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135587817/250000000 : ℝ)^8385 ≤ (22252311876087/50000000000000 : ℝ)^6337 := by
    have hnat : (135587817 : ℕ)^8385*50000000000000^6337 ≤ 22252311876087^6337*250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135587817 250000000 22252311876087 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048789039/10000000000 : ℝ)^8385 ≤ (12273997049203/100000000000000 : ℝ)^6337 := by
    have hnat : (2048789039 : ℕ)^8385*100000000000000^6337 ≤ 12273997049203^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048789039 10000000000 12273997049203 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304905573/10000000000 : ℝ), (135587817/250000000 : ℝ), (-2048789039/10000000000 : ℝ)] ![(8644275837171/20000000000000 : ℝ), (22252311876087/50000000000000 : ℝ), (12273997049203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304905573/10000000000 : ℝ)|^8385 ≤ (8644275837171/20000000000000 : ℝ)^6337
        have hw : |(5304905573/10000000000 : ℝ)|=(5304905573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135587817/250000000 : ℝ)|^8385 ≤ (22252311876087/50000000000000 : ℝ)^6337
        have hw : |(135587817/250000000 : ℝ)|=(135587817/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2048789039/10000000000 : ℝ)|^8385 ≤ (12273997049203/100000000000000 : ℝ)^6337
        have hw : |(-2048789039/10000000000 : ℝ)|=(2048789039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s3_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435575059/1000000000 : ℝ)*x 0 + (4546805097/10000000000 : ℝ)*x 1 + (834530471/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435575059/1000000000 : ℝ)^8385 ≤ (1331910068937/4000000000000 : ℝ)^6337 := by
    have hnat : (435575059 : ℕ)^8385*4000000000000^6337 ≤ 1331910068937^6337*1000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435575059 1000000000 1331910068937 4000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4546805097/10000000000 : ℝ)^8385 ≤ (35243856318789/100000000000000 : ℝ)^6337 := by
    have hnat : (4546805097 : ℕ)^8385*100000000000000^6337 ≤ 35243856318789^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546805097 10000000000 35243856318789 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834530471/2000000000 : ℝ)^8385 ≤ (15729195973413/50000000000000 : ℝ)^6337 := by
    have hnat : (834530471 : ℕ)^8385*50000000000000^6337 ≤ 15729195973413^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834530471 2000000000 15729195973413 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435575059/1000000000 : ℝ), (4546805097/10000000000 : ℝ), (834530471/2000000000 : ℝ)] ![(1331910068937/4000000000000 : ℝ), (35243856318789/100000000000000 : ℝ), (15729195973413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435575059/1000000000 : ℝ)|^8385 ≤ (1331910068937/4000000000000 : ℝ)^6337
        have hw : |(435575059/1000000000 : ℝ)|=(435575059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4546805097/10000000000 : ℝ)|^8385 ≤ (35243856318789/100000000000000 : ℝ)^6337
        have hw : |(4546805097/10000000000 : ℝ)|=(4546805097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834530471/2000000000 : ℝ)|^8385 ≤ (15729195973413/50000000000000 : ℝ)^6337
        have hw : |(834530471/2000000000 : ℝ)|=(834530471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1192_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5389/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8179/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8179/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8179/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8179/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8179/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8179/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9291/100000 : ℝ) ^ (131/32 : ℝ) ≤ (1192712282442689/20000000000000000000 : ℝ) := by
    have hpowers : (9291/100000 : ℝ)^131 ≤ (1192712282442689/20000000000000000000 : ℝ)^32 := by
      have hnat : (9291 : ℕ)^131*20000000000000000000^32 ≤ 1192712282442689^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9291 100000 1192712282442689 20000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9291/100000 : ℝ)) (X := (1192712282442689/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hpowhi : (8179/50000 : ℝ) ^ (131/32 : ℝ) ≤ (30211899153668987/50000000000000000000 : ℝ) := by
    have hpowers : (8179/50000 : ℝ)^131 ≤ (30211899153668987/50000000000000000000 : ℝ)^32 := by
      have hnat : (8179 : ℕ)^131*50000000000000000000^32 ≤ 30211899153668987^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8179 50000 30211899153668987 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8179/50000 : ℝ)) (X := (30211899153668987/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001192712282442689/10000000000000000000 : ℝ) ≤ (1250036417054439/1250000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (10001192712282442689/10000000000000000000 : ℝ)^32 ≤ (1250036417054439/1250000000000000 : ℝ)^131 := by
      have hnat : (10001192712282442689 : ℕ)^32*1250000000000000^131 ≤ 1250036417054439^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001192712282442689 10000000000000000000 1250036417054439 1250000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250036417054439/1250000000000000 : ℝ)) (X := (10001192712282442689/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100066387359719551419/100000000000000000000 : ℝ) ≤ (2500405317329579/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100066387359719551419/100000000000000000000 : ℝ)^32 ≤ (2500405317329579/2500000000000000 : ℝ)^131 := by
      have hnat : (100066387359719551419 : ℕ)^32*2500000000000000^131 ≤ 2500405317329579^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100066387359719551419 100000000000000000000 2500405317329579 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500405317329579/2500000000000000 : ℝ)) (X := (100066387359719551419/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (25030211899153668987/25000000000000000000 : ℝ) ≤ (62518445013757/62500000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (25030211899153668987/25000000000000000000 : ℝ)^32 ≤ (62518445013757/62500000000000 : ℝ)^131 := by
      have hnat : (25030211899153668987 : ℕ)^32*62500000000000^131 ≤ 62518445013757^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25030211899153668987 25000000000000000000 62518445013757 62500000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62518445013757/62500000000000 : ℝ)) (X := (25030211899153668987/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1192712282442689/20000000000000000000 : ℝ) ≤ ((4415459128860093711/4416875000000000000 : ℝ)+2*(332483220701/176675000000000 : ℝ)*(9291/100000 : ℝ))^(131/32 : ℝ) := by
    rw [show (4415459128860093711/4416875000000000000 : ℝ)+2*(332483220701/176675000000000 : ℝ)*(9291/100000 : ℝ)=(1250036417054439/1250000000000000 : ℝ) by norm_num, show 1+2*(1192712282442689/20000000000000000000 : ℝ)=(10001192712282442689/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30211899153668987/50000000000000000000 : ℝ)+(1192712282442689/20000000000000000000 : ℝ) ≤ ((4415459128860093711/4416875000000000000 : ℝ)+(332483220701/176675000000000 : ℝ)*((8179/50000 : ℝ)+(9291/100000 : ℝ)))^(131/32 : ℝ) := by
    rw [show (4415459128860093711/4416875000000000000 : ℝ)+(332483220701/176675000000000 : ℝ)*((8179/50000 : ℝ)+(9291/100000 : ℝ))=(2500405317329579/2500000000000000 : ℝ) by norm_num, show 1+(30211899153668987/50000000000000000000 : ℝ)+(1192712282442689/20000000000000000000 : ℝ)=(100066387359719551419/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30211899153668987/50000000000000000000 : ℝ) ≤ ((4415459128860093711/4416875000000000000 : ℝ)+2*(332483220701/176675000000000 : ℝ)*(8179/50000 : ℝ))^(131/32 : ℝ) := by
    rw [show (4415459128860093711/4416875000000000000 : ℝ)+2*(332483220701/176675000000000 : ℝ)*(8179/50000 : ℝ)=(62518445013757/62500000000000 : ℝ) by norm_num, show 1+2*(30211899153668987/50000000000000000000 : ℝ)=(25030211899153668987/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4415459128860093711/4416875000000000000 : ℝ)*(X 1 0+X 2 0)+(332483220701/176675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (9291/100000 : ℝ)) (hi := (8179/50000 : ℝ)) (c := (4415459128860093711/4416875000000000000 : ℝ)) (alpha := (332483220701/176675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4415459128860093711/4416875000000000000 : ℝ)*(X 0 1+X 2 1)+(332483220701/176675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (9291/100000 : ℝ)) (hi := (8179/50000 : ℝ)) (c := (4415459128860093711/4416875000000000000 : ℝ)) (alpha := (332483220701/176675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4415459128860093711/4416875000000000000 : ℝ)*(X 0 2+X 1 2)+(332483220701/176675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (9291/100000 : ℝ)) (hi := (8179/50000 : ℝ)) (c := (4415459128860093711/4416875000000000000 : ℝ)) (alpha := (332483220701/176675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-267489011/1250000000 : ℝ)*X 0 0+(2712110189/5000000000 : ℝ)*X 0 1+(5236570039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214104643/400000000 : ℝ)*X 1 0+(-447146313/2000000000 : ℝ)*X 1 1+(5236570261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352615953/10000000000 : ℝ)*X 2 0+(2618285247/5000000000 : ℝ)*X 2 1+(-111786571/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177859127/5000000000 : ℝ)*X 0 0+(4171230301/10000000000 : ℝ)*X 0 1+(4548219971/10000000000 : ℝ)*X 0 2+(2177859127/5000000000 : ℝ)*X 1 0+(4171230301/10000000000 : ℝ)*X 1 1+(4548219971/10000000000 : ℝ)*X 1 2+(2177859127/5000000000 : ℝ)*X 2 0+(4171230301/10000000000 : ℝ)*X 2 1+(4548219971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2139928083/10000000000 : ℝ)*X 0 0+(5237274163/10000000000 : ℝ)*X 0 1+(5423512347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304905943/10000000000 : ℝ)*X 1 0+(-409757817/2000000000 : ℝ)*X 1 1+(5423512279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304905573/10000000000 : ℝ)*X 2 0+(135587817/250000000 : ℝ)*X 2 1+(-2048789039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435575059/1000000000 : ℝ)*X 0 0+(4546805097/10000000000 : ℝ)*X 0 1+(834530471/2000000000 : ℝ)*X 0 2+(435575059/1000000000 : ℝ)*X 1 0+(4546805097/10000000000 : ℝ)*X 1 1+(834530471/2000000000 : ℝ)*X 1 2+(435575059/1000000000 : ℝ)*X 2 0+(4546805097/10000000000 : ℝ)*X 2 1+(834530471/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168554849545544333410923/17667500000000000000000000000 : ℝ) := by norm_num
    linear_combination (294384483/20000000000000 : ℝ)*(base19) + (583852737/50000000000000 : ℝ)*(base23) + (19564053/20000000000000 : ℝ)*(lower2) + (37255191/25000000000000 : ℝ)*(upper3) + (18269409/12500000000000 : ℝ)*(upper5) + (1995438698807869/50000000000000 : ℝ)*(major0) + (1995438698807869/50000000000000 : ℝ)*(major1) + (1995438698807869/50000000000000 : ℝ)*(major2) + (5329095090165531/100000000000000 : ℝ)*(sp0) + (1065825896191319/20000000000000 : ℝ)*(sp1) + (166535305786673/3125000000000 : ℝ)*(sp2) + (1326303915251409/50000000000000 : ℝ)*(sp3) + (17931356739/50000000000000 : ℝ)*(sp4) + (15693836623/100000000000000 : ℝ)*(sp7) + (2652623524339441/100000000000000 : ℝ)*(f.failure) + (5329130952879009/100000000000000 : ℝ)*(f.sum) + (34737488417637/8833750000000000000000000000 : ℝ)*base66 + (596449680859906891/220843750000000000000000000000000 : ℝ)*base68 + (2518485438690749359/220843750000000000000000000000000 : ℝ)*base69 + (26981915078780609/220843750000000000000000000000000 : ℝ)*base71 + (89235696334719/17667500000000000000000000000 : ℝ)*base74 + (389448738879250641/220843750000000000000000000000000 : ℝ)*base76 + (1053552487366875641/220843750000000000000000000000000 : ℝ)*base78 + (3104320212790593109/220843750000000000000000000000000 : ℝ)*base79 + (190951090766147/35335000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (168309/50000000000000000000 : ℝ)*base90 + (168309/50000000000000000000 : ℝ)*base92 + (168309/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101933395198966010858397111/11042187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1229884343/50000000000000 : ℝ)*(base19) + (2384974957/100000000000000 : ℝ)*(base23) + (36409759/20000000000000 : ℝ)*(upper3) + (149831247/100000000000000 : ℝ)*(lower4) + (153645637/50000000000000 : ℝ)*(upper5) + (402108430033397/10000000000000 : ℝ)*(major0) + (402108430033397/10000000000000 : ℝ)*(major1) + (402108430033397/10000000000000 : ℝ)*(major2) + (12131421253/25000000000000 : ℝ)*(sp1) + (50445680989/100000000000000 : ℝ)*(sp2) + (1073893418654069/20000000000000 : ℝ)*(sp4) + (5369416107816647/100000000000000 : ℝ)*(sp5) + (5369414262614399/100000000000000 : ℝ)*(sp6) + (334087649961081/12500000000000 : ℝ)*(sp7) + (334087649961081/12500000000000 : ℝ)*(f.failure) + (1073893418654069/20000000000000 : ℝ)*(f.sum) + (39756813931519/7067000000000000000000000000 : ℝ)*base66 + (221482449386485017/44168750000000000000000000000000 : ℝ)*base67 + (4265807808435017/44168750000000000000000000000000 : ℝ)*base69 + (148000302369297517/44168750000000000000000000000000 : ℝ)*base71 + (44301130941051/7067000000000000000000000000 : ℝ)*base74 + (240070090718997517/44168750000000000000000000000000 : ℝ)*base75 + (261383156599041267/44168750000000000000000000000000 : ℝ)*base77 + (194158704338878767/44168750000000000000000000000000 : ℝ)*base79 + (32827729362257/7067000000000000000000000000 : ℝ)*base82 + (18331/6250000000000000000 : ℝ)*base89 + (18331/6250000000000000000 : ℝ)*base91 + (18331/6250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1192_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1192_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1192_s4_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2142536107/10000000000 : ℝ)*x 0 + (1079920323/2000000000 : ℝ)*x 1 + (164358459/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142536107/10000000000 : ℝ)^8385 ≤ (13022567836567/100000000000000 : ℝ)^6337 := by
    have hnat : (2142536107 : ℕ)^8385*100000000000000^6337 ≤ 13022567836567^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142536107 10000000000 13022567836567 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079920323/2000000000 : ℝ)^8385 ≤ (44245186141451/100000000000000 : ℝ)^6337 := by
    have hnat : (1079920323 : ℕ)^8385*100000000000000^6337 ≤ 44245186141451^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079920323 2000000000 44245186141451 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164358459/312500000 : ℝ)^8385 ≤ (5341530751249/12500000000000 : ℝ)^6337 := by
    have hnat : (164358459 : ℕ)^8385*12500000000000^6337 ≤ 5341530751249^6337*312500000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164358459 312500000 5341530751249 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2142536107/10000000000 : ℝ), (1079920323/2000000000 : ℝ), (164358459/312500000 : ℝ)] ![(13022567836567/100000000000000 : ℝ), (44245186141451/100000000000000 : ℝ), (5341530751249/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2142536107/10000000000 : ℝ)|^8385 ≤ (13022567836567/100000000000000 : ℝ)^6337
        have hw : |(-2142536107/10000000000 : ℝ)|=(2142536107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079920323/2000000000 : ℝ)|^8385 ≤ (44245186141451/100000000000000 : ℝ)^6337
        have hw : |(1079920323/2000000000 : ℝ)|=(1079920323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164358459/312500000 : ℝ)|^8385 ≤ (5341530751249/12500000000000 : ℝ)^6337
        have hw : |(164358459/312500000 : ℝ)|=(164358459/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s4_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346438853/10000000000 : ℝ)*x 0 + (-2213713729/10000000000 : ℝ)*x 1 + (5259470543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346438853/10000000000 : ℝ)^8385 ≤ (8733939127877/20000000000000 : ℝ)^6337 := by
    have hnat : (5346438853 : ℕ)^8385*20000000000000^6337 ≤ 8733939127877^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346438853 10000000000 8733939127877 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213713729/10000000000 : ℝ)^8385 ≤ (13598059888417/100000000000000 : ℝ)^6337 := by
    have hnat : (2213713729 : ℕ)^8385*100000000000000^6337 ≤ 13598059888417^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213713729 10000000000 13598059888417 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259470543/10000000000 : ℝ)^8385 ≤ (21366122225577/50000000000000 : ℝ)^6337 := by
    have hnat : (5259470543 : ℕ)^8385*50000000000000^6337 ≤ 21366122225577^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259470543 10000000000 21366122225577 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346438853/10000000000 : ℝ), (-2213713729/10000000000 : ℝ), (5259470543/10000000000 : ℝ)] ![(8733939127877/20000000000000 : ℝ), (13598059888417/100000000000000 : ℝ), (21366122225577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346438853/10000000000 : ℝ)|^8385 ≤ (8733939127877/20000000000000 : ℝ)^6337
        have hw : |(5346438853/10000000000 : ℝ)|=(5346438853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2213713729/10000000000 : ℝ)|^8385 ≤ (13598059888417/100000000000000 : ℝ)^6337
        have hw : |(-2213713729/10000000000 : ℝ)|=(2213713729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259470543/10000000000 : ℝ)|^8385 ≤ (21366122225577/50000000000000 : ℝ)^6337
        have hw : |(5259470543/10000000000 : ℝ)|=(5259470543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s4_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336609517/2500000000 : ℝ)*x 0 + (5259470507/10000000000 : ℝ)*x 1 + (-1106857411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336609517/2500000000 : ℝ)^8385 ≤ (10917421788827/25000000000000 : ℝ)^6337 := by
    have hnat : (1336609517 : ℕ)^8385*25000000000000^6337 ≤ 10917421788827^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336609517 2500000000 10917421788827 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259470507/10000000000 : ℝ)^8385 ≤ (10683061016033/25000000000000 : ℝ)^6337 := by
    have hnat : (5259470507 : ℕ)^8385*25000000000000^6337 ≤ 10683061016033^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259470507 10000000000 10683061016033 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106857411/5000000000 : ℝ)^8385 ≤ (13598068772141/100000000000000 : ℝ)^6337 := by
    have hnat : (1106857411 : ℕ)^8385*100000000000000^6337 ≤ 13598068772141^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106857411 5000000000 13598068772141 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336609517/2500000000 : ℝ), (5259470507/10000000000 : ℝ), (-1106857411/5000000000 : ℝ)] ![(10917421788827/25000000000000 : ℝ), (10683061016033/25000000000000 : ℝ), (13598068772141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336609517/2500000000 : ℝ)|^8385 ≤ (10917421788827/25000000000000 : ℝ)^6337
        have hw : |(1336609517/2500000000 : ℝ)|=(1336609517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259470507/10000000000 : ℝ)|^8385 ≤ (10683061016033/25000000000000 : ℝ)^6337
        have hw : |(5259470507/10000000000 : ℝ)|=(5259470507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1106857411/5000000000 : ℝ)|^8385 ≤ (13598068772141/100000000000000 : ℝ)^6337
        have hw : |(-1106857411/5000000000 : ℝ)|=(1106857411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s4_3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357286591/10000000000 : ℝ)*x 0 + (1054690521/2500000000 : ℝ)*x 1 + (4500285539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357286591/10000000000 : ℝ)^8385 ≤ (26650631561/80000000000 : ℝ)^6337 := by
    have hnat : (4357286591 : ℕ)^8385*80000000000^6337 ≤ 26650631561^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357286591 10000000000 26650631561 80000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054690521/2500000000 : ℝ)^8385 ≤ (6383837680849/20000000000000 : ℝ)^6337 := by
    have hnat : (1054690521 : ℕ)^8385*20000000000000^6337 ≤ 6383837680849^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054690521 2500000000 6383837680849 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500285539/10000000000 : ℝ)^8385 ≤ (34767522131027/100000000000000 : ℝ)^6337 := by
    have hnat : (4500285539 : ℕ)^8385*100000000000000^6337 ≤ 34767522131027^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500285539 10000000000 34767522131027 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357286591/10000000000 : ℝ), (1054690521/2500000000 : ℝ), (4500285539/10000000000 : ℝ)] ![(26650631561/80000000000 : ℝ), (6383837680849/20000000000000 : ℝ), (34767522131027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357286591/10000000000 : ℝ)|^8385 ≤ (26650631561/80000000000 : ℝ)^6337
        have hw : |(4357286591/10000000000 : ℝ)|=(4357286591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054690521/2500000000 : ℝ)|^8385 ≤ (6383837680849/20000000000000 : ℝ)^6337
        have hw : |(1054690521/2500000000 : ℝ)|=(1054690521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500285539/10000000000 : ℝ)|^8385 ≤ (34767522131027/100000000000000 : ℝ)^6337
        have hw : |(4500285539/10000000000 : ℝ)|=(4500285539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s4_4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071271297/5000000000 : ℝ)*x 0 + (5259864091/10000000000 : ℝ)*x 1 + (16872521/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071271297/5000000000 : ℝ)^8385 ≤ (6511310003951/50000000000000 : ℝ)^6337 := by
    have hnat : (1071271297 : ℕ)^8385*50000000000000^6337 ≤ 6511310003951^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071271297 5000000000 6511310003951 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259864091/10000000000 : ℝ)^8385 ≤ (1335514855709/3125000000000 : ℝ)^6337 := by
    have hnat : (5259864091 : ℕ)^8385*3125000000000^6337 ≤ 1335514855709^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259864091 10000000000 1335514855709 3125000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16872521/31250000 : ℝ)^8385 ≤ (4424090459983/10000000000000 : ℝ)^6337 := by
    have hnat : (16872521 : ℕ)^8385*10000000000000^6337 ≤ 4424090459983^6337*31250000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16872521 31250000 4424090459983 10000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071271297/5000000000 : ℝ), (5259864091/10000000000 : ℝ), (16872521/31250000 : ℝ)] ![(6511310003951/50000000000000 : ℝ), (1335514855709/3125000000000 : ℝ), (4424090459983/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071271297/5000000000 : ℝ)|^8385 ≤ (6511310003951/50000000000000 : ℝ)^6337
        have hw : |(-1071271297/5000000000 : ℝ)|=(1071271297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259864091/10000000000 : ℝ)|^8385 ≤ (1335514855709/3125000000000 : ℝ)^6337
        have hw : |(5259864091/10000000000 : ℝ)|=(5259864091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16872521/31250000 : ℝ)|^8385 ≤ (4424090459983/10000000000000 : ℝ)^6337
        have hw : |(16872521/31250000 : ℝ)|=(16872521/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s4_5 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655404353/5000000000 : ℝ)*x 0 + (-259247267/1250000000 : ℝ)*x 1 + (2699603339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655404353/5000000000 : ℝ)^8385 ≤ (5410628694917/12500000000000 : ℝ)^6337 := by
    have hnat : (2655404353 : ℕ)^8385*12500000000000^6337 ≤ 5410628694917^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655404353 5000000000 5410628694917 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259247267/1250000000 : ℝ)^8385 ≤ (6237033141857/50000000000000 : ℝ)^6337 := by
    have hnat : (259247267 : ℕ)^8385*50000000000000^6337 ≤ 6237033141857^6337*1250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259247267 1250000000 6237033141857 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699603339/5000000000 : ℝ)^8385 ≤ (44240904144461/100000000000000 : ℝ)^6337 := by
    have hnat : (2699603339 : ℕ)^8385*100000000000000^6337 ≤ 44240904144461^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699603339 5000000000 44240904144461 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655404353/5000000000 : ℝ), (-259247267/1250000000 : ℝ), (2699603339/5000000000 : ℝ)] ![(5410628694917/12500000000000 : ℝ), (6237033141857/50000000000000 : ℝ), (44240904144461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655404353/5000000000 : ℝ)|^8385 ≤ (5410628694917/12500000000000 : ℝ)^6337
        have hw : |(2655404353/5000000000 : ℝ)|=(2655404353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259247267/1250000000 : ℝ)|^8385 ≤ (6237033141857/50000000000000 : ℝ)^6337
        have hw : |(-259247267/1250000000 : ℝ)|=(259247267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699603339/5000000000 : ℝ)|^8385 ≤ (44240904144461/100000000000000 : ℝ)^6337
        have hw : |(2699603339/5000000000 : ℝ)|=(2699603339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s4_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655404107/5000000000 : ℝ)*x 0 + (21596829/40000000 : ℝ)*x 1 + (-2073978023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655404107/5000000000 : ℝ)^8385 ≤ (21642512126703/50000000000000 : ℝ)^6337 := by
    have hnat : (2655404107 : ℕ)^8385*50000000000000^6337 ≤ 21642512126703^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655404107 5000000000 21642512126703 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21596829/40000000 : ℝ)^8385 ≤ (44240910346143/100000000000000 : ℝ)^6337 := by
    have hnat : (21596829 : ℕ)^8385*100000000000000^6337 ≤ 44240910346143^6337*40000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21596829 40000000 44240910346143 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073978023/10000000000 : ℝ)^8385 ≤ (623703269221/5000000000000 : ℝ)^6337 := by
    have hnat : (2073978023 : ℕ)^8385*5000000000000^6337 ≤ 623703269221^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073978023 10000000000 623703269221 5000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655404107/5000000000 : ℝ), (21596829/40000000 : ℝ), (-2073978023/10000000000 : ℝ)] ![(21642512126703/50000000000000 : ℝ), (44240910346143/100000000000000 : ℝ), (623703269221/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655404107/5000000000 : ℝ)|^8385 ≤ (21642512126703/50000000000000 : ℝ)^6337
        have hw : |(2655404107/5000000000 : ℝ)|=(2655404107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21596829/40000000 : ℝ)|^8385 ≤ (44240910346143/100000000000000 : ℝ)^6337
        have hw : |(21596829/40000000 : ℝ)|=(21596829/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2073978023/10000000000 : ℝ)|^8385 ≤ (623703269221/5000000000000 : ℝ)^6337
        have hw : |(-2073978023/10000000000 : ℝ)|=(2073978023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s4_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357300961/10000000000 : ℝ)*x 0 + (281218457/625000000 : ℝ)*x 1 + (843910883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357300961/10000000000 : ℝ)^8385 ≤ (33313434822241/100000000000000 : ℝ)^6337 := by
    have hnat : (4357300961 : ℕ)^8385*100000000000000^6337 ≤ 33313434822241^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357300961 10000000000 33313434822241 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281218457/625000000 : ℝ)^8385 ≤ (8689861085203/25000000000000 : ℝ)^6337 := by
    have hnat : (281218457 : ℕ)^8385*25000000000000^6337 ≤ 8689861085203^6337*625000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281218457 625000000 8689861085203 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (843910883/2000000000 : ℝ)^8385 ≤ (7981780207397/25000000000000 : ℝ)^6337 := by
    have hnat : (843910883 : ℕ)^8385*25000000000000^6337 ≤ 7981780207397^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843910883 2000000000 7981780207397 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357300961/10000000000 : ℝ), (281218457/625000000 : ℝ), (843910883/2000000000 : ℝ)] ![(33313434822241/100000000000000 : ℝ), (8689861085203/25000000000000 : ℝ), (7981780207397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357300961/10000000000 : ℝ)|^8385 ≤ (33313434822241/100000000000000 : ℝ)^6337
        have hw : |(4357300961/10000000000 : ℝ)|=(4357300961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281218457/625000000 : ℝ)|^8385 ≤ (8689861085203/25000000000000 : ℝ)^6337
        have hw : |(281218457/625000000 : ℝ)|=(281218457/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(843910883/2000000000 : ℝ)|^8385 ≤ (7981780207397/25000000000000 : ℝ)^6337
        have hw : |(843910883/2000000000 : ℝ)|=(843910883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1192_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11267/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5389/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5389/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5389/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5389/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5389/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5389/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5389/50000 : ℝ) ^ (131/32 : ℝ) ≤ (10950984678600899/100000000000000000000 : ℝ) := by
    have hpowers : (5389/50000 : ℝ)^131 ≤ (10950984678600899/100000000000000000000 : ℝ)^32 := by
      have hnat : (5389 : ℕ)^131*100000000000000000000^32 ≤ 10950984678600899^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5389 50000 10950984678600899 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5389/50000 : ℝ)) (X := (10950984678600899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (131/32 : ℝ) ≤ (9889682333173427/25000000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^131 ≤ (9889682333173427/25000000000000000000 : ℝ)^32 := by
      have hnat : (59 : ℕ)^131*25000000000000000000^32 ≤ 9889682333173427^32*400^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 9889682333173427 25000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (9889682333173427/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010950984678600899/50000000000000000000 : ℝ) ≤ (10000534965667097/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50010950984678600899/50000000000000000000 : ℝ)^32 ≤ (10000534965667097/10000000000000000 : ℝ)^131 := by
      have hnat : (50010950984678600899 : ℕ)^32*10000000000000000^131 ≤ 10000534965667097^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010950984678600899 50000000000000000000 10000534965667097 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000534965667097/10000000000000000 : ℝ)) (X := (50010950984678600899/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050509714011294607/100000000000000000000 : ℝ) ≤ (10001233589660129/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100050509714011294607/100000000000000000000 : ℝ)^32 ≤ (10001233589660129/10000000000000000 : ℝ)^131 := by
      have hnat : (100050509714011294607 : ℕ)^32*10000000000000000^131 ≤ 10001233589660129^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050509714011294607 100000000000000000000 10001233589660129 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001233589660129/10000000000000000 : ℝ)) (X := (100050509714011294607/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509889682333173427/12500000000000000000 : ℝ) ≤ (10001932213653161/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (12509889682333173427/12500000000000000000 : ℝ)^32 ≤ (10001932213653161/10000000000000000 : ℝ)^131 := by
      have hnat : (12509889682333173427 : ℕ)^32*10000000000000000^131 ≤ 10001932213653161^131*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509889682333173427 12500000000000000000 10001932213653161 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001932213653161/10000000000000000 : ℝ)) (X := (12509889682333173427/12500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10950984678600899/100000000000000000000 : ℝ) ≤ ((3308922112069659291/3310000000000000000 : ℝ)+2*(29109333043/16550000000000 : ℝ)*(5389/50000 : ℝ))^(131/32 : ℝ) := by
    rw [show (3308922112069659291/3310000000000000000 : ℝ)+2*(29109333043/16550000000000 : ℝ)*(5389/50000 : ℝ)=(10000534965667097/10000000000000000 : ℝ) by norm_num, show 1+2*(10950984678600899/100000000000000000000 : ℝ)=(50010950984678600899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9889682333173427/25000000000000000000 : ℝ)+(10950984678600899/100000000000000000000 : ℝ) ≤ ((3308922112069659291/3310000000000000000 : ℝ)+(29109333043/16550000000000 : ℝ)*((59/400 : ℝ)+(5389/50000 : ℝ)))^(131/32 : ℝ) := by
    rw [show (3308922112069659291/3310000000000000000 : ℝ)+(29109333043/16550000000000 : ℝ)*((59/400 : ℝ)+(5389/50000 : ℝ))=(10001233589660129/10000000000000000 : ℝ) by norm_num, show 1+(9889682333173427/25000000000000000000 : ℝ)+(10950984678600899/100000000000000000000 : ℝ)=(100050509714011294607/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9889682333173427/25000000000000000000 : ℝ) ≤ ((3308922112069659291/3310000000000000000 : ℝ)+2*(29109333043/16550000000000 : ℝ)*(59/400 : ℝ))^(131/32 : ℝ) := by
    rw [show (3308922112069659291/3310000000000000000 : ℝ)+2*(29109333043/16550000000000 : ℝ)*(59/400 : ℝ)=(10001932213653161/10000000000000000 : ℝ) by norm_num, show 1+2*(9889682333173427/25000000000000000000 : ℝ)=(12509889682333173427/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3308922112069659291/3310000000000000000 : ℝ)*(X 1 0+X 2 0)+(29109333043/16550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (59/400 : ℝ)) (c := (3308922112069659291/3310000000000000000 : ℝ)) (alpha := (29109333043/16550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3308922112069659291/3310000000000000000 : ℝ)*(X 0 1+X 2 1)+(29109333043/16550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (59/400 : ℝ)) (c := (3308922112069659291/3310000000000000000 : ℝ)) (alpha := (29109333043/16550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3308922112069659291/3310000000000000000 : ℝ)*(X 0 2+X 1 2)+(29109333043/16550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (59/400 : ℝ)) (c := (3308922112069659291/3310000000000000000 : ℝ)) (alpha := (29109333043/16550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2142536107/10000000000 : ℝ)*X 0 0+(1079920323/2000000000 : ℝ)*X 0 1+(164358459/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346438853/10000000000 : ℝ)*X 1 0+(-2213713729/10000000000 : ℝ)*X 1 1+(5259470543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336609517/2500000000 : ℝ)*X 2 0+(5259470507/10000000000 : ℝ)*X 2 1+(-1106857411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357286591/10000000000 : ℝ)*X 0 0+(1054690521/2500000000 : ℝ)*X 0 1+(4500285539/10000000000 : ℝ)*X 0 2+(4357286591/10000000000 : ℝ)*X 1 0+(1054690521/2500000000 : ℝ)*X 1 1+(4500285539/10000000000 : ℝ)*X 1 2+(4357286591/10000000000 : ℝ)*X 2 0+(1054690521/2500000000 : ℝ)*X 2 1+(4500285539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1071271297/5000000000 : ℝ)*X 0 0+(5259864091/10000000000 : ℝ)*X 0 1+(16872521/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655404353/5000000000 : ℝ)*X 1 0+(-259247267/1250000000 : ℝ)*X 1 1+(2699603339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655404107/5000000000 : ℝ)*X 2 0+(21596829/40000000 : ℝ)*X 2 1+(-2073978023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357300961/10000000000 : ℝ)*X 0 0+(281218457/625000000 : ℝ)*X 0 1+(843910883/2000000000 : ℝ)*X 0 2+(4357300961/10000000000 : ℝ)*X 1 0+(281218457/625000000 : ℝ)*X 1 1+(843910883/2000000000 : ℝ)*X 1 2+(4357300961/10000000000 : ℝ)*X 2 0+(281218457/625000000 : ℝ)*X 2 1+(843910883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1477040556315740357013/331000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1065464673/100000000000000 : ℝ)*(base19) + (180513873/25000000000000 : ℝ)*(base23) + (518555701/100000000000000 : ℝ)*(upper2) + (1047597/12500000000000 : ℝ)*(lower5) + (1068840992900843/20000000000000 : ℝ)*(major0) + (1068840992900843/20000000000000 : ℝ)*(major1) + (1068840992900843/20000000000000 : ℝ)*(major2) + (892029861568669/12500000000000 : ℝ)*(sp0) + (7136266567759647/100000000000000 : ℝ)*(sp1) + (7136227068073407/100000000000000 : ℝ)*(sp2) + (1776063574298417/50000000000000 : ℝ)*(sp3) + (3592584371/12500000000000 : ℝ)*(sp4) + (39843095421/100000000000000 : ℝ)*(sp6) + (7499220999/50000000000000 : ℝ)*(sp7) + (3552142147038831/100000000000000 : ℝ)*(f.failure) + (11150418176913/156250000000 : ℝ)*(f.sum) + (357805328549/165500000000000000000000000 : ℝ)*base66 + (25998991206482313/66200000000000000000000000000000 : ℝ)*base67 + (445447673871917687/66200000000000000000000000000000 : ℝ)*base70 + (722328778724117687/66200000000000000000000000000000 : ℝ)*base72 + (1906577935041/331000000000000000000000000 : ℝ)*base74 + (620253220081082313/66200000000000000000000000000000 : ℝ)*base75 + (705744412913917687/66200000000000000000000000000000 : ℝ)*base78 + (216633010754282313/66200000000000000000000000000000 : ℝ)*base79 + (720727964431/331000000000000000000000000 : ℝ)*base82 + (158581/50000000000000000000 : ℝ)*base89 + (158581/50000000000000000000 : ℝ)*base91 + (158581/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (924831315276157948399003539/82750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2273115133/100000000000000 : ℝ)*(base19) + (426928997/25000000000000 : ℝ)*(base23) + (108547547/25000000000000 : ℝ)*(upper3) + (4097009/100000000000000 : ℝ)*(lower4) + (59691009/50000000000000 : ℝ)*(upper5) + (5374360565564957/100000000000000 : ℝ)*(major0) + (5374360565564957/100000000000000 : ℝ)*(major1) + (5374360565564957/100000000000000 : ℝ)*(major2) + (20806416953/50000000000000 : ℝ)*(sp1) + (2211436491/4000000000000 : ℝ)*(sp2) + (7176535034964793/100000000000000 : ℝ)*(sp4) + (7176491149015753/100000000000000 : ℝ)*(sp5) + (717647804133653/10000000000000 : ℝ)*(sp6) + (1786092861812399/50000000000000 : ℝ)*(sp7) + (1786092861812399/50000000000000 : ℝ)*(f.failure) + (7176535034964793/100000000000000 : ℝ)*(f.sum) + (1174975585139/827500000000000000000000000 : ℝ)*base66 + (1844954101740265487/331000000000000000000000000000000 : ℝ)*base67 + (5755488397719265487/331000000000000000000000000000000 : ℝ)*base69 + (1027837182815265487/331000000000000000000000000000000 : ℝ)*base71 + (1357698833067/413750000000000000000000000 : ℝ)*base74 + (8815775201627265487/331000000000000000000000000000000 : ℝ)*base75 + (3214738730411265487/331000000000000000000000000000000 : ℝ)*base77 + (1884643927481734513/331000000000000000000000000000000 : ℝ)*base80 + (676270737447/103437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (289851/25000000000000000000 : ℝ)*base90 + (289851/25000000000000000000 : ℝ)*base92 + (289851/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1192_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1192_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1192_s5_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-107153483/500000000 : ℝ)*x 0 + (2696818479/5000000000 : ℝ)*x 1 + (1316271261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107153483/500000000 : ℝ)^8385 ≤ (203544673083/1562500000000 : ℝ)^6337 := by
    have hnat : (107153483 : ℕ)^8385*1562500000000^6337 ≤ 203544673083^6337*500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107153483 500000000 203544673083 1562500000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696818479/5000000000 : ℝ)^8385 ≤ (44180526752797/100000000000000 : ℝ)^6337 := by
    have hnat : (2696818479 : ℕ)^8385*100000000000000^6337 ≤ 44180526752797^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696818479 5000000000 44180526752797 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316271261/2500000000 : ℝ)^8385 ≤ (5349076770169/12500000000000 : ℝ)^6337 := by
    have hnat : (1316271261 : ℕ)^8385*12500000000000^6337 ≤ 5349076770169^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316271261 2500000000 5349076770169 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107153483/500000000 : ℝ), (2696818479/5000000000 : ℝ), (1316271261/2500000000 : ℝ)] ![(203544673083/1562500000000 : ℝ), (44180526752797/100000000000000 : ℝ), (5349076770169/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107153483/500000000 : ℝ)|^8385 ≤ (203544673083/1562500000000 : ℝ)^6337
        have hw : |(-107153483/500000000 : ℝ)|=(107153483/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696818479/5000000000 : ℝ)|^8385 ≤ (44180526752797/100000000000000 : ℝ)^6337
        have hw : |(2696818479/5000000000 : ℝ)|=(2696818479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316271261/2500000000 : ℝ)|^8385 ≤ (5349076770169/12500000000000 : ℝ)^6337
        have hw : |(1316271261/2500000000 : ℝ)|=(1316271261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s5_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344936061/10000000000 : ℝ)*x 0 + (-2208282243/10000000000 : ℝ)*x 1 + (105301701/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344936061/10000000000 : ℝ)^8385 ≤ (43653454590721/100000000000000 : ℝ)^6337 := by
    have hnat : (5344936061 : ℕ)^8385*100000000000000^6337 ≤ 43653454590721^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344936061 10000000000 43653454590721 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2208282243/10000000000 : ℝ)^8385 ≤ (2710786236339/20000000000000 : ℝ)^6337 := by
    have hnat : (2208282243 : ℕ)^8385*20000000000000^6337 ≤ 2710786236339^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208282243 10000000000 2710786236339 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105301701/200000000 : ℝ)^8385 ≤ (21396307112939/50000000000000 : ℝ)^6337 := by
    have hnat : (105301701 : ℕ)^8385*50000000000000^6337 ≤ 21396307112939^6337*200000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105301701 200000000 21396307112939 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344936061/10000000000 : ℝ), (-2208282243/10000000000 : ℝ), (105301701/200000000 : ℝ)] ![(43653454590721/100000000000000 : ℝ), (2710786236339/20000000000000 : ℝ), (21396307112939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344936061/10000000000 : ℝ)|^8385 ≤ (43653454590721/100000000000000 : ℝ)^6337
        have hw : |(5344936061/10000000000 : ℝ)|=(5344936061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2208282243/10000000000 : ℝ)|^8385 ≤ (2710786236339/20000000000000 : ℝ)^6337
        have hw : |(-2208282243/10000000000 : ℝ)|=(2208282243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105301701/200000000 : ℝ)|^8385 ≤ (21396307112939/50000000000000 : ℝ)^6337
        have hw : |(105301701/200000000 : ℝ)|=(105301701/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s5_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068987209/2000000000 : ℝ)*x 0 + (2632542531/5000000000 : ℝ)*x 1 + (-1104141123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068987209/2000000000 : ℝ)^8385 ≤ (10913363604453/25000000000000 : ℝ)^6337 := by
    have hnat : (1068987209 : ℕ)^8385*25000000000000^6337 ≤ 10913363604453^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068987209 2000000000 10913363604453 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632542531/5000000000 : ℝ)^8385 ≤ (4279261435493/10000000000000 : ℝ)^6337 := by
    have hnat : (2632542531 : ℕ)^8385*10000000000000^6337 ≤ 4279261435493^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632542531 5000000000 4279261435493 10000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104141123/5000000000 : ℝ)^8385 ≤ (677696560303/5000000000000 : ℝ)^6337 := by
    have hnat : (1104141123 : ℕ)^8385*5000000000000^6337 ≤ 677696560303^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104141123 5000000000 677696560303 5000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068987209/2000000000 : ℝ), (2632542531/5000000000 : ℝ), (-1104141123/5000000000 : ℝ)] ![(10913363604453/25000000000000 : ℝ), (4279261435493/10000000000000 : ℝ), (677696560303/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068987209/2000000000 : ℝ)|^8385 ≤ (10913363604453/25000000000000 : ℝ)^6337
        have hw : |(1068987209/2000000000 : ℝ)|=(1068987209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632542531/5000000000 : ℝ)|^8385 ≤ (4279261435493/10000000000000 : ℝ)^6337
        have hw : |(2632542531/5000000000 : ℝ)|=(2632542531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1104141123/5000000000 : ℝ)|^8385 ≤ (677696560303/5000000000000 : ℝ)^6337
        have hw : |(-1104141123/5000000000 : ℝ)|=(1104141123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s5_3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357601191/10000000000 : ℝ)*x 0 + (2115176137/5000000000 : ℝ)*x 1 + (4488613543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357601191/10000000000 : ℝ)^8385 ≤ (33316472069417/100000000000000 : ℝ)^6337 := by
    have hnat : (4357601191 : ℕ)^8385*100000000000000^6337 ≤ 33316472069417^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357601191 10000000000 33316472069417 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115176137/5000000000 : ℝ)^8385 ≤ (32035271600849/100000000000000 : ℝ)^6337 := by
    have hnat : (2115176137 : ℕ)^8385*100000000000000^6337 ≤ 32035271600849^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115176137 5000000000 32035271600849 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488613543/10000000000 : ℝ)^8385 ≤ (34648256310541/100000000000000 : ℝ)^6337 := by
    have hnat : (4488613543 : ℕ)^8385*100000000000000^6337 ≤ 34648256310541^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488613543 10000000000 34648256310541 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357601191/10000000000 : ℝ), (2115176137/5000000000 : ℝ), (4488613543/10000000000 : ℝ)] ![(33316472069417/100000000000000 : ℝ), (32035271600849/100000000000000 : ℝ), (34648256310541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357601191/10000000000 : ℝ)|^8385 ≤ (33316472069417/100000000000000 : ℝ)^6337
        have hw : |(4357601191/10000000000 : ℝ)|=(4357601191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115176137/5000000000 : ℝ)|^8385 ≤ (32035271600849/100000000000000 : ℝ)^6337
        have hw : |(2115176137/5000000000 : ℝ)|=(2115176137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488613543/10000000000 : ℝ)|^8385 ≤ (34648256310541/100000000000000 : ℝ)^6337
        have hw : |(4488613543/10000000000 : ℝ)|=(4488613543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s5_4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071537379/5000000000 : ℝ)*x 0 + (2632708099/5000000000 : ℝ)*x 1 + (1078660917/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071537379/5000000000 : ℝ)^8385 ≤ (13026900080987/100000000000000 : ℝ)^6337 := by
    have hnat : (1071537379 : ℕ)^8385*100000000000000^6337 ≤ 13026900080987^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071537379 5000000000 13026900080987 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632708099/5000000000 : ℝ)^8385 ≤ (42796175532257/100000000000000 : ℝ)^6337 := by
    have hnat : (2632708099 : ℕ)^8385*100000000000000^6337 ≤ 42796175532257^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632708099 5000000000 42796175532257 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078660917/2000000000 : ℝ)^8385 ≤ (44176924369247/100000000000000 : ℝ)^6337 := by
    have hnat : (1078660917 : ℕ)^8385*100000000000000^6337 ≤ 44176924369247^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078660917 2000000000 44176924369247 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071537379/5000000000 : ℝ), (2632708099/5000000000 : ℝ), (1078660917/2000000000 : ℝ)] ![(13026900080987/100000000000000 : ℝ), (42796175532257/100000000000000 : ℝ), (44176924369247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071537379/5000000000 : ℝ)|^8385 ≤ (13026900080987/100000000000000 : ℝ)^6337
        have hw : |(-1071537379/5000000000 : ℝ)|=(1071537379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632708099/5000000000 : ℝ)|^8385 ≤ (42796175532257/100000000000000 : ℝ)^6337
        have hw : |(2632708099/5000000000 : ℝ)|=(2632708099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078660917/2000000000 : ℝ)|^8385 ≤ (44176924369247/100000000000000 : ℝ)^6337
        have hw : |(1078660917/2000000000 : ℝ)|=(1078660917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s5_5 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312249001/10000000000 : ℝ)*x 0 + (-1040031357/5000000000 : ℝ)*x 1 + (5393304603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312249001/10000000000 : ℝ)^8385 ≤ (43300562972841/100000000000000 : ℝ)^6337 := by
    have hnat : (5312249001 : ℕ)^8385*100000000000000^6337 ≤ 43300562972841^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312249001 10000000000 43300562972841 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040031357/5000000000 : ℝ)^8385 ≤ (12522512447997/100000000000000 : ℝ)^6337 := by
    have hnat : (1040031357 : ℕ)^8385*100000000000000^6337 ≤ 12522512447997^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040031357 5000000000 12522512447997 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393304603/10000000000 : ℝ)^8385 ≤ (2761057785271/6250000000000 : ℝ)^6337 := by
    have hnat : (5393304603 : ℕ)^8385*6250000000000^6337 ≤ 2761057785271^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393304603 10000000000 2761057785271 6250000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312249001/10000000000 : ℝ), (-1040031357/5000000000 : ℝ), (5393304603/10000000000 : ℝ)] ![(43300562972841/100000000000000 : ℝ), (12522512447997/100000000000000 : ℝ), (2761057785271/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312249001/10000000000 : ℝ)|^8385 ≤ (43300562972841/100000000000000 : ℝ)^6337
        have hw : |(5312249001/10000000000 : ℝ)|=(5312249001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040031357/5000000000 : ℝ)|^8385 ≤ (12522512447997/100000000000000 : ℝ)^6337
        have hw : |(-1040031357/5000000000 : ℝ)|=(1040031357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393304603/10000000000 : ℝ)|^8385 ≤ (2761057785271/6250000000000 : ℝ)^6337
        have hw : |(5393304603/10000000000 : ℝ)|=(5393304603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s5_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664031131/1250000000 : ℝ)*x 0 + (107866091/200000000 : ℝ)*x 1 + (-1040031361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664031131/1250000000 : ℝ)^8385 ≤ (43300563479753/100000000000000 : ℝ)^6337 := by
    have hnat : (664031131 : ℕ)^8385*100000000000000^6337 ≤ 43300563479753^6337*1250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664031131 1250000000 43300563479753 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107866091/200000000 : ℝ)^8385 ≤ (11044230997477/25000000000000 : ℝ)^6337 := by
    have hnat : (107866091 : ℕ)^8385*25000000000000^6337 ≤ 11044230997477^6337*200000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107866091 200000000 11044230997477 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040031361/5000000000 : ℝ)^8385 ≤ (3130628127931/25000000000000 : ℝ)^6337 := by
    have hnat : (1040031361 : ℕ)^8385*25000000000000^6337 ≤ 3130628127931^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040031361 5000000000 3130628127931 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664031131/1250000000 : ℝ), (107866091/200000000 : ℝ), (-1040031361/5000000000 : ℝ)] ![(43300563479753/100000000000000 : ℝ), (11044230997477/25000000000000 : ℝ), (3130628127931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664031131/1250000000 : ℝ)|^8385 ≤ (43300563479753/100000000000000 : ℝ)^6337
        have hw : |(664031131/1250000000 : ℝ)|=(664031131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107866091/200000000 : ℝ)|^8385 ≤ (11044230997477/25000000000000 : ℝ)^6337
        have hw : |(107866091/200000000 : ℝ)|=(107866091/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040031361/5000000000 : ℝ)|^8385 ≤ (3130628127931/25000000000000 : ℝ)^6337
        have hw : |(-1040031361/5000000000 : ℝ)|=(1040031361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s5_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178805741/5000000000 : ℝ)*x 0 + (4487948377/10000000000 : ℝ)*x 1 + (2115509939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178805741/5000000000 : ℝ)^8385 ≤ (16658288089251/50000000000000 : ℝ)^6337 := by
    have hnat : (2178805741 : ℕ)^8385*50000000000000^6337 ≤ 16658288089251^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178805741 5000000000 16658288089251 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487948377/10000000000 : ℝ)^8385 ≤ (34641462582311/100000000000000 : ℝ)^6337 := by
    have hnat : (4487948377 : ℕ)^8385*100000000000000^6337 ≤ 34641462582311^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487948377 10000000000 34641462582311 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115509939/5000000000 : ℝ)^8385 ≤ (32041961217649/100000000000000 : ℝ)^6337 := by
    have hnat : (2115509939 : ℕ)^8385*100000000000000^6337 ≤ 32041961217649^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115509939 5000000000 32041961217649 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178805741/5000000000 : ℝ), (4487948377/10000000000 : ℝ), (2115509939/5000000000 : ℝ)] ![(16658288089251/50000000000000 : ℝ), (34641462582311/100000000000000 : ℝ), (32041961217649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178805741/5000000000 : ℝ)|^8385 ≤ (16658288089251/50000000000000 : ℝ)^6337
        have hw : |(2178805741/5000000000 : ℝ)|=(2178805741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487948377/10000000000 : ℝ)|^8385 ≤ (34641462582311/100000000000000 : ℝ)^6337
        have hw : |(4487948377/10000000000 : ℝ)|=(4487948377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115509939/5000000000 : ℝ)|^8385 ≤ (32041961217649/100000000000000 : ℝ)^6337
        have hw : |(2115509939/5000000000 : ℝ)|=(2115509939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1192_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5693/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1411/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11267/100000 : ℝ) ^ (131/32 : ℝ) ≤ (13132282143638093/100000000000000000000 : ℝ) := by
    have hpowers : (11267/100000 : ℝ)^131 ≤ (13132282143638093/100000000000000000000 : ℝ)^32 := by
      have hnat : (11267 : ℕ)^131*100000000000000000000^32 ≤ 13132282143638093^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11267 100000 13132282143638093 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11267/100000 : ℝ)) (X := (13132282143638093/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (131/32 : ℝ) ≤ (4275305582583269/12500000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^131 ≤ (4275305582583269/12500000000000000000 : ℝ)^32 := by
      have hnat : (2847 : ℕ)^131*12500000000000000000^32 ≤ 4275305582583269^32*20000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 4275305582583269 12500000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (4275305582583269/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013132282143638093/50000000000000000000 : ℝ) ≤ (5000320756740011/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50013132282143638093/50000000000000000000 : ℝ)^32 ≤ (5000320756740011/5000000000000000 : ℝ)^131 := by
      have hnat : (50013132282143638093 : ℕ)^32*5000000000000000^131 ≤ 5000320756740011^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013132282143638093 50000000000000000000 5000320756740011 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000320756740011/5000000000000000 : ℝ)) (X := (50013132282143638093/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009466945360860849/20000000000000000000 : ℝ) ≤ (10001156061382569/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (20009466945360860849/20000000000000000000 : ℝ)^32 ≤ (10001156061382569/10000000000000000 : ℝ)^131 := by
      have hnat : (20009466945360860849 : ℕ)^32*10000000000000000^131 ≤ 10001156061382569^131*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009466945360860849 20000000000000000000 10001156061382569 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001156061382569/10000000000000000 : ℝ)) (X := (20009466945360860849/20000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254275305582583269/6250000000000000000 : ℝ) ≤ (2500417652321279/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (6254275305582583269/6250000000000000000 : ℝ)^32 ≤ (2500417652321279/2500000000000000 : ℝ)^131 := by
      have hnat : (6254275305582583269 : ℕ)^32*2500000000000000^131 ≤ 2500417652321279^131*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254275305582583269 6250000000000000000 2500417652321279 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500417652321279/2500000000000000 : ℝ)) (X := (6254275305582583269/6250000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13132282143638093/100000000000000000000 : ℝ) ≤ ((2119307799255193657/2120000000000000000 : ℝ)+2*(73506843221/42400000000000 : ℝ)*(11267/100000 : ℝ))^(131/32 : ℝ) := by
    rw [show (2119307799255193657/2120000000000000000 : ℝ)+2*(73506843221/42400000000000 : ℝ)*(11267/100000 : ℝ)=(5000320756740011/5000000000000000 : ℝ) by norm_num, show 1+2*(13132282143638093/100000000000000000000 : ℝ)=(50013132282143638093/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4275305582583269/12500000000000000000 : ℝ)+(13132282143638093/100000000000000000000 : ℝ) ≤ ((2119307799255193657/2120000000000000000 : ℝ)+(73506843221/42400000000000 : ℝ)*((2847/20000 : ℝ)+(11267/100000 : ℝ)))^(131/32 : ℝ) := by
    rw [show (2119307799255193657/2120000000000000000 : ℝ)+(73506843221/42400000000000 : ℝ)*((2847/20000 : ℝ)+(11267/100000 : ℝ))=(10001156061382569/10000000000000000 : ℝ) by norm_num, show 1+(4275305582583269/12500000000000000000 : ℝ)+(13132282143638093/100000000000000000000 : ℝ)=(20009466945360860849/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4275305582583269/12500000000000000000 : ℝ) ≤ ((2119307799255193657/2120000000000000000 : ℝ)+2*(73506843221/42400000000000 : ℝ)*(2847/20000 : ℝ))^(131/32 : ℝ) := by
    rw [show (2119307799255193657/2120000000000000000 : ℝ)+2*(73506843221/42400000000000 : ℝ)*(2847/20000 : ℝ)=(2500417652321279/2500000000000000 : ℝ) by norm_num, show 1+2*(4275305582583269/12500000000000000000 : ℝ)=(6254275305582583269/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2119307799255193657/2120000000000000000 : ℝ)*(X 1 0+X 2 0)+(73506843221/42400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (2119307799255193657/2120000000000000000 : ℝ)) (alpha := (73506843221/42400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2119307799255193657/2120000000000000000 : ℝ)*(X 0 1+X 2 1)+(73506843221/42400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (2119307799255193657/2120000000000000000 : ℝ)) (alpha := (73506843221/42400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2119307799255193657/2120000000000000000 : ℝ)*(X 0 2+X 1 2)+(73506843221/42400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (2119307799255193657/2120000000000000000 : ℝ)) (alpha := (73506843221/42400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-107153483/500000000 : ℝ)*X 0 0+(2696818479/5000000000 : ℝ)*X 0 1+(1316271261/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344936061/10000000000 : ℝ)*X 1 0+(-2208282243/10000000000 : ℝ)*X 1 1+(105301701/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068987209/2000000000 : ℝ)*X 2 0+(2632542531/5000000000 : ℝ)*X 2 1+(-1104141123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357601191/10000000000 : ℝ)*X 0 0+(2115176137/5000000000 : ℝ)*X 0 1+(4488613543/10000000000 : ℝ)*X 0 2+(4357601191/10000000000 : ℝ)*X 1 0+(2115176137/5000000000 : ℝ)*X 1 1+(4488613543/10000000000 : ℝ)*X 1 2+(4357601191/10000000000 : ℝ)*X 2 0+(2115176137/5000000000 : ℝ)*X 2 1+(4488613543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1071537379/5000000000 : ℝ)*X 0 0+(2632708099/5000000000 : ℝ)*X 0 1+(1078660917/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312249001/10000000000 : ℝ)*X 1 0+(-1040031357/5000000000 : ℝ)*X 1 1+(5393304603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664031131/1250000000 : ℝ)*X 2 0+(107866091/200000000 : ℝ)*X 2 1+(-1040031361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178805741/5000000000 : ℝ)*X 0 0+(4487948377/10000000000 : ℝ)*X 0 1+(2115509939/5000000000 : ℝ)*X 0 2+(2178805741/5000000000 : ℝ)*X 1 0+(4487948377/10000000000 : ℝ)*X 1 1+(2115509939/5000000000 : ℝ)*X 1 2+(2178805741/5000000000 : ℝ)*X 2 0+(4487948377/10000000000 : ℝ)*X 2 1+(2115509939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2134506564829405693203219/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2146655117/100000000000000 : ℝ)*(base19) + (984973727/50000000000000 : ℝ)*(base23) + (16400519/20000000000000 : ℝ)*(lower2) + (280103951/100000000000000 : ℝ)*(upper3) + (9749019/6250000000000 : ℝ)*(upper5) + (582559237207117/10000000000000 : ℝ)*(major0) + (582559237207117/10000000000000 : ℝ)*(major1) + (582559237207117/10000000000000 : ℝ)*(major2) + (3889509916501241/50000000000000 : ℝ)*(sp0) + (1944768869198131/25000000000000 : ℝ)*(sp1) + (1944768913375047/25000000000000 : ℝ)*(sp2) + (96801891038617/2500000000000 : ℝ)*(sp3) + (28895222579/50000000000000 : ℝ)*(sp4) + (7780849729/25000000000000 : ℝ)*(sp7) + (968026691235899/25000000000000 : ℝ)*(f.failure) + (7779077623447641/100000000000000 : ℝ)*(f.sum) + (11568854563/4000000000000000000000000 : ℝ)*base66 + (433254927851073/400000000000000000000000000000 : ℝ)*base67 + (245406354251073/400000000000000000000000000000 : ℝ)*base69 + (1646470937748927/400000000000000000000000000000 : ℝ)*base72 + (12237702189/4000000000000000000000000 : ℝ)*base73 + (5610048670548927/400000000000000000000000000000 : ℝ)*base76 + (3691538336148927/400000000000000000000000000000 : ℝ)*base78 + (10874022118548927/400000000000000000000000000000 : ℝ)*base80 + (22888978509/4000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (8649/12500000000000000000 : ℝ)*base89 + (8649/12500000000000000000 : ℝ)*base91 + (8649/12500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23786784371976927762279/2120000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1011435941/50000000000000 : ℝ)*(base19) + (585123567/25000000000000 : ℝ)*(base23) + (132210529/50000000000000 : ℝ)*(upper3) + (105051621/100000000000000 : ℝ)*(lower4) + (196332259/100000000000000 : ℝ)*(upper5) + (5855723833681131/100000000000000 : ℝ)*(major0) + (5855723833681131/100000000000000 : ℝ)*(major1) + (5855723833681131/100000000000000 : ℝ)*(major2) + (26576647161/50000000000000 : ℝ)*(sp1) + (61391088341/100000000000000 : ℝ)*(sp2) + (977414124579751/12500000000000 : ℝ)*(sp4) + (1563851564094361/20000000000000 : ℝ)*(sp5) + (39096246325277/500000000000 : ℝ)*(sp6) + (973033574179551/25000000000000 : ℝ)*(sp7) + (973033574179551/25000000000000 : ℝ)*(f.failure) + (977414124579751/12500000000000 : ℝ)*(f.sum) + (14968783516729/2120000000000000000000000000 : ℝ)*base66 + (1114564435336067/212000000000000000000000000000000 : ℝ)*base67 + (161488896835336067/212000000000000000000000000000000 : ℝ)*base69 + (878312840439336067/212000000000000000000000000000000 : ℝ)*base71 + (9697267048089/2120000000000000000000000000 : ℝ)*base74 + (1623262324184663933/212000000000000000000000000000000 : ℝ)*base76 + (784434556336663933/212000000000000000000000000000000 : ℝ)*base78 + (2559395689860663933/212000000000000000000000000000000 : ℝ)*base80 + (1348101860169/2120000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (44301/12500000000000000000 : ℝ)*base89 + (44301/12500000000000000000 : ℝ)*base91 + (44301/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1192_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1192_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1192_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1192_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1192_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1192_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1192_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
