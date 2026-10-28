-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1179_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:49:14.067206+00:00
-- url     : https://prove2.me/submissions/72ddbab1-ef89-466d-9d45-dd6236b949db

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
theorem support_rectangle_w1179_s9_0 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149319831/10000000000 : ℝ)*x 0 + (1078462599/2000000000 : ℝ)*x 1 + (1316591009/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149319831/10000000000 : ℝ)^2093 ≤ (13063803292237/100000000000000 : ℝ)^1581 := by
    have hnat : (2149319831 : ℕ)^2093*100000000000000^1581 ≤ 13063803292237^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149319831 10000000000 13063803292237 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078462599/2000000000 : ℝ)^2093 ≤ (44148059445447/100000000000000 : ℝ)^1581 := by
    have hnat : (1078462599 : ℕ)^2093*100000000000000^1581 ≤ 44148059445447^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078462599 2000000000 44148059445447 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316591009/2500000000 : ℝ)^2093 ≤ (10697034312267/25000000000000 : ℝ)^1581 := by
    have hnat : (1316591009 : ℕ)^2093*25000000000000^1581 ≤ 10697034312267^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316591009 2500000000 10697034312267 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149319831/10000000000 : ℝ), (1078462599/2000000000 : ℝ), (1316591009/2500000000 : ℝ)] ![(13063803292237/100000000000000 : ℝ), (44148059445447/100000000000000 : ℝ), (10697034312267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149319831/10000000000 : ℝ)|^2093 ≤ (13063803292237/100000000000000 : ℝ)^1581
        have hw : |(-2149319831/10000000000 : ℝ)|=(2149319831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078462599/2000000000 : ℝ)|^2093 ≤ (44148059445447/100000000000000 : ℝ)^1581
        have hw : |(1078462599/2000000000 : ℝ)|=(1078462599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316591009/2500000000 : ℝ)|^2093 ≤ (10697034312267/25000000000000 : ℝ)^1581
        have hw : |(1316591009/2500000000 : ℝ)|=(1316591009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s9_1 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672299307/5000000000 : ℝ)*x 0 + (5266364057/10000000000 : ℝ)*x 1 + (-2213193523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672299307/5000000000 : ℝ)^2093 ≤ (5453955498619/12500000000000 : ℝ)^1581 := by
    have hnat : (2672299307 : ℕ)^2093*12500000000000^1581 ≤ 5453955498619^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672299307 5000000000 5453955498619 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266364057/10000000000 : ℝ)^2093 ≤ (334282324023/781250000000 : ℝ)^1581 := by
    have hnat : (5266364057 : ℕ)^2093*781250000000^1581 ≤ 334282324023^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266364057 10000000000 334282324023 781250000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2213193523/10000000000 : ℝ)^2093 ≤ (3395054628257/25000000000000 : ℝ)^1581 := by
    have hnat : (2213193523 : ℕ)^2093*25000000000000^1581 ≤ 3395054628257^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213193523 10000000000 3395054628257 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672299307/5000000000 : ℝ), (5266364057/10000000000 : ℝ), (-2213193523/10000000000 : ℝ)] ![(5453955498619/12500000000000 : ℝ), (334282324023/781250000000 : ℝ), (3395054628257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672299307/5000000000 : ℝ)|^2093 ≤ (5453955498619/12500000000000 : ℝ)^1581
        have hw : |(2672299307/5000000000 : ℝ)|=(2672299307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266364057/10000000000 : ℝ)|^2093 ≤ (334282324023/781250000000 : ℝ)^1581
        have hw : |(5266364057/10000000000 : ℝ)|=(5266364057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2213193523/10000000000 : ℝ)|^2093 ≤ (3395054628257/25000000000000 : ℝ)^1581
        have hw : |(-2213193523/10000000000 : ℝ)|=(2213193523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s9_2 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149324381/10000000000 : ℝ)*x 0 + (5266680637/10000000000 : ℝ)*x 1 + (168499857/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149324381/10000000000 : ℝ)^2093 ≤ (6531919951867/50000000000000 : ℝ)^1581 := by
    have hnat : (2149324381 : ℕ)^2093*50000000000000^1581 ≤ 6531919951867^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149324381 10000000000 6531919951867 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266680637/10000000000 : ℝ)^2093 ≤ (42791542635271/100000000000000 : ℝ)^1581 := by
    have hnat : (5266680637 : ℕ)^2093*100000000000000^1581 ≤ 42791542635271^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266680637 10000000000 42791542635271 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168499857/312500000 : ℝ)^2093 ≤ (44144617447719/100000000000000 : ℝ)^1581 := by
    have hnat : (168499857 : ℕ)^2093*100000000000000^1581 ≤ 44144617447719^1581*312500000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168499857 312500000 44144617447719 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149324381/10000000000 : ℝ), (5266680637/10000000000 : ℝ), (168499857/312500000 : ℝ)] ![(6531919951867/50000000000000 : ℝ), (42791542635271/100000000000000 : ℝ), (44144617447719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149324381/10000000000 : ℝ)|^2093 ≤ (6531919951867/50000000000000 : ℝ)^1581
        have hw : |(-2149324381/10000000000 : ℝ)|=(2149324381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266680637/10000000000 : ℝ)|^2093 ≤ (42791542635271/100000000000000 : ℝ)^1581
        have hw : |(5266680637/10000000000 : ℝ)|=(5266680637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168499857/312500000 : ℝ)|^2093 ≤ (44144617447719/100000000000000 : ℝ)^1581
        have hw : |(168499857/312500000 : ℝ)|=(168499857/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s9_3 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656301271/5000000000 : ℝ)*x 0 + (-1043781237/5000000000 : ℝ)*x 1 + (5391995259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656301271/5000000000 : ℝ)^2093 ≤ (43286183216511/100000000000000 : ℝ)^1581 := by
    have hnat : (2656301271 : ℕ)^2093*100000000000000^1581 ≤ 43286183216511^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656301271 5000000000 43286183216511 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043781237/5000000000 : ℝ)^2093 ≤ (6284600556847/50000000000000 : ℝ)^1581 := by
    have hnat : (1043781237 : ℕ)^2093*50000000000000^1581 ≤ 6284600556847^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043781237 5000000000 6284600556847 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391995259/10000000000 : ℝ)^2093 ≤ (44144615659381/100000000000000 : ℝ)^1581 := by
    have hnat : (5391995259 : ℕ)^2093*100000000000000^1581 ≤ 44144615659381^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391995259 10000000000 44144615659381 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656301271/5000000000 : ℝ), (-1043781237/5000000000 : ℝ), (5391995259/10000000000 : ℝ)] ![(43286183216511/100000000000000 : ℝ), (6284600556847/50000000000000 : ℝ), (44144615659381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656301271/5000000000 : ℝ)|^2093 ≤ (43286183216511/100000000000000 : ℝ)^1581
        have hw : |(2656301271/5000000000 : ℝ)|=(2656301271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1043781237/5000000000 : ℝ)|^2093 ≤ (6284600556847/50000000000000 : ℝ)^1581
        have hw : |(-1043781237/5000000000 : ℝ)|=(1043781237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391995259/10000000000 : ℝ)|^2093 ≤ (44144615659381/100000000000000 : ℝ)^1581
        have hw : |(5391995259/10000000000 : ℝ)|=(5391995259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s9_4 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312602693/10000000000 : ℝ)*x 0 + (168499853/312500000 : ℝ)*x 1 + (-2087562219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312602693/10000000000 : ℝ)^2093 ≤ (10821546211317/25000000000000 : ℝ)^1581 := by
    have hnat : (5312602693 : ℕ)^2093*25000000000000^1581 ≤ 10821546211317^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312602693 10000000000 10821546211317 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168499853/312500000 : ℝ)^2093 ≤ (22072308030201/50000000000000 : ℝ)^1581 := by
    have hnat : (168499853 : ℕ)^2093*50000000000000^1581 ≤ 22072308030201^1581*312500000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168499853 312500000 22072308030201 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087562219/10000000000 : ℝ)^2093 ≤ (12569199081123/100000000000000 : ℝ)^1581 := by
    have hnat : (2087562219 : ℕ)^2093*100000000000000^1581 ≤ 12569199081123^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087562219 10000000000 12569199081123 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312602693/10000000000 : ℝ), (168499853/312500000 : ℝ), (-2087562219/10000000000 : ℝ)] ![(10821546211317/25000000000000 : ℝ), (22072308030201/50000000000000 : ℝ), (12569199081123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312602693/10000000000 : ℝ)|^2093 ≤ (10821546211317/25000000000000 : ℝ)^1581
        have hw : |(5312602693/10000000000 : ℝ)|=(5312602693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168499853/312500000 : ℝ)|^2093 ≤ (22072308030201/50000000000000 : ℝ)^1581
        have hw : |(168499853/312500000 : ℝ)|=(168499853/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087562219/10000000000 : ℝ)|^2093 ≤ (12569199081123/100000000000000 : ℝ)^1581
        have hw : |(-2087562219/10000000000 : ℝ)|=(2087562219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s9_5 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (13623433/31250000 : ℝ)*x 0 + (4486852321/10000000000 : ℝ)*x 1 + (264733239/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13623433/31250000 : ℝ)^2093 ≤ (16658643263929/50000000000000 : ℝ)^1581 := by
    have hnat : (13623433 : ℕ)^2093*50000000000000^1581 ≤ 16658643263929^1581*31250000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13623433 31250000 16658643263929 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486852321/10000000000 : ℝ)^2093 ≤ (17305917613871/50000000000000 : ℝ)^1581 := by
    have hnat : (4486852321 : ℕ)^2093*50000000000000^1581 ≤ 17305917613871^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486852321 10000000000 17305917613871 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264733239/625000000 : ℝ)^2093 ≤ (6414175645093/20000000000000 : ℝ)^1581 := by
    have hnat : (264733239 : ℕ)^2093*20000000000000^1581 ≤ 6414175645093^1581*625000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264733239 625000000 6414175645093 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13623433/31250000 : ℝ), (4486852321/10000000000 : ℝ), (264733239/625000000 : ℝ)] ![(16658643263929/50000000000000 : ℝ), (17305917613871/50000000000000 : ℝ), (6414175645093/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13623433/31250000 : ℝ)|^2093 ≤ (16658643263929/50000000000000 : ℝ)^1581
        have hw : |(13623433/31250000 : ℝ)|=(13623433/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486852321/10000000000 : ℝ)|^2093 ≤ (17305917613871/50000000000000 : ℝ)^1581
        have hw : |(4486852321/10000000000 : ℝ)|=(4486852321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264733239/625000000 : ℝ)|^2093 ≤ (6414175645093/20000000000000 : ℝ)^1581
        have hw : |(264733239/625000000 : ℝ)|=(264733239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1179_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11401/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (11401/100000 : ℝ) ^ (8371/2048 : ℝ) ≤ (2794965049692037/20000000000000000000 : ℝ) := by
    have hpowers : (11401/100000 : ℝ)^8371 ≤ (2794965049692037/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11401 : ℕ)^8371*20000000000000000000^2048 ≤ 2794965049692037^2048*100000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11401 100000 2794965049692037 20000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11401/100000 : ℝ)) (X := (2794965049692037/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1407/10000 : ℝ) ^ (8371/2048 : ℝ) ≤ (6603364845441149/20000000000000000000 : ℝ) := by
    have hpowers : (1407/10000 : ℝ)^8371 ≤ (6603364845441149/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1407 : ℕ)^8371*20000000000000000000^2048 ≤ 6603364845441149^2048*10000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 10000 6603364845441149 20000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/10000 : ℝ)) (X := (6603364845441149/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002794965049692037/10000000000000000000 : ℝ) ≤ (5000341863833219/5000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (10002794965049692037/10000000000000000000 : ℝ)^2048 ≤ (5000341863833219/5000000000000000 : ℝ)^8371 := by
      have hnat : (10002794965049692037 : ℕ)^2048*5000000000000000^8371 ≤ 5000341863833219^8371*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002794965049692037 10000000000000000000 5000341863833219 5000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000341863833219/5000000000000000 : ℝ)) (X := (10002794965049692037/10000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004699164947566593/10000000000000000000 : ℝ) ≤ (5000574733143281/5000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (10004699164947566593/10000000000000000000 : ℝ)^2048 ≤ (5000574733143281/5000000000000000 : ℝ)^8371 := by
      have hnat : (10004699164947566593 : ℕ)^2048*5000000000000000^8371 ≤ 5000574733143281^8371*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004699164947566593 10000000000000000000 5000574733143281 5000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000574733143281/5000000000000000 : ℝ)) (X := (10004699164947566593/10000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006603364845441149/10000000000000000000 : ℝ) ≤ (5000807602453343/5000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (10006603364845441149/10000000000000000000 : ℝ)^2048 ≤ (5000807602453343/5000000000000000 : ℝ)^8371 := by
      have hnat : (10006603364845441149 : ℕ)^2048*5000000000000000^8371 ≤ 5000807602453343^8371*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006603364845441149 10000000000000000000 5000807602453343 5000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000807602453343/5000000000000000 : ℝ)) (X := (10006603364845441149/10000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2794965049692037/20000000000000000000 : ℝ) ≤ ((13340602548562827787/13345000000000000000 : ℝ)+2*(116434655031/66725000000000 : ℝ)*(11401/100000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (13340602548562827787/13345000000000000000 : ℝ)+2*(116434655031/66725000000000 : ℝ)*(11401/100000 : ℝ)=(5000341863833219/5000000000000000 : ℝ) by norm_num, show 1+2*(2794965049692037/20000000000000000000 : ℝ)=(10002794965049692037/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6603364845441149/20000000000000000000 : ℝ)+(2794965049692037/20000000000000000000 : ℝ) ≤ ((13340602548562827787/13345000000000000000 : ℝ)+(116434655031/66725000000000 : ℝ)*((1407/10000 : ℝ)+(11401/100000 : ℝ)))^(8371/2048 : ℝ) := by
    rw [show (13340602548562827787/13345000000000000000 : ℝ)+(116434655031/66725000000000 : ℝ)*((1407/10000 : ℝ)+(11401/100000 : ℝ))=(5000574733143281/5000000000000000 : ℝ) by norm_num, show 1+(6603364845441149/20000000000000000000 : ℝ)+(2794965049692037/20000000000000000000 : ℝ)=(10004699164947566593/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6603364845441149/20000000000000000000 : ℝ) ≤ ((13340602548562827787/13345000000000000000 : ℝ)+2*(116434655031/66725000000000 : ℝ)*(1407/10000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (13340602548562827787/13345000000000000000 : ℝ)+2*(116434655031/66725000000000 : ℝ)*(1407/10000 : ℝ)=(5000807602453343/5000000000000000 : ℝ) by norm_num, show 1+2*(6603364845441149/20000000000000000000 : ℝ)=(10006603364845441149/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13340602548562827787/13345000000000000000 : ℝ)*(X 1 0+X 2 0)+(116434655031/66725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (13340602548562827787/13345000000000000000 : ℝ)) (alpha := (116434655031/66725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13340602548562827787/13345000000000000000 : ℝ)*(X 0 1+X 2 1)+(116434655031/66725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (13340602548562827787/13345000000000000000 : ℝ)) (alpha := (116434655031/66725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13340602548562827787/13345000000000000000 : ℝ)*(X 0 2+X 1 2)+(116434655031/66725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (13340602548562827787/13345000000000000000 : ℝ)) (alpha := (116434655031/66725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2149319831/10000000000 : ℝ)*X 0 0+(1078462599/2000000000 : ℝ)*X 0 1+(1316591009/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672299307/5000000000 : ℝ)*X 2 0+(5266364057/10000000000 : ℝ)*X 2 1+(-2213193523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s9_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-2149324381/10000000000 : ℝ)*X 0 0+(5266680637/10000000000 : ℝ)*X 0 1+(168499857/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656301271/5000000000 : ℝ)*X 1 0+(-1043781237/5000000000 : ℝ)*X 1 1+(5391995259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5312602693/10000000000 : ℝ)*X 2 0+(168499853/312500000 : ℝ)*X 2 1+(-2087562219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((13623433/31250000 : ℝ)*X 0 0+(4486852321/10000000000 : ℝ)*X 0 1+(264733239/625000000 : ℝ)*X 0 2+(13623433/31250000 : ℝ)*X 1 0+(4486852321/10000000000 : ℝ)*X 1 1+(264733239/625000000 : ℝ)*X 1 2+(13623433/31250000 : ℝ)*X 2 0+(4486852321/10000000000 : ℝ)*X 2 1+(264733239/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10132678530717362570787/3336250000000000000000000000 : ℝ) := by norm_num
    linear_combination (36468157/100000000000000 : ℝ)*(base8) + (6190427/50000000000000 : ℝ)*(lower1) + (16111229/10000000000000 : ℝ)*(lower2) + (5729701/50000000000000 : ℝ)*(lower3) + (10042859/100000000000000 : ℝ)*(lower4) + (5981041982623999/100000000000000 : ℝ)*(major0) + (5981041982623999/100000000000000 : ℝ)*(major1) + (5981041982623999/100000000000000 : ℝ)*(major2) + (1797746203/20000000000000 : ℝ)*(sp0) + (9555122961/100000000000000 : ℝ)*(sp1) + (3989960211444683/50000000000000 : ℝ)*(sp2) + (3989964724044269/50000000000000 : ℝ)*(sp3) + (7979919892965577/100000000000000 : ℝ)*(sp4) + (3185723532737/80000000000 : ℝ)*(sp5) + (3185723532737/80000000000 : ℝ)*(f.failure) + (3989964724044269/50000000000000 : ℝ)*(f.sum) + (7345506036829/13345000000000000000000000000 : ℝ)*base66 + (6632740036932439787/1334500000000000000000000000000000 : ℝ)*base68 + (13066574584926060213/1334500000000000000000000000000000 : ℝ)*base69 + (1508649078742060213/1334500000000000000000000000000000 : ℝ)*base71 + (13791253634883/6672500000000000000000000000 : ℝ)*base73 + (951285143294939787/1334500000000000000000000000000000 : ℝ)*base76 + (6757489373536560213/1334500000000000000000000000000000 : ℝ)*base77 + (7233655380851439787/1334500000000000000000000000000000 : ℝ)*base80 + (4751255516427/6672500000000000000000000000 : ℝ)*base82 + (40621/4000000000000000000 : ℝ)*base90 + (40621/4000000000000000000 : ℝ)*base92 + (40621/4000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1179_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1179_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1179_s10_0 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149323713/10000000000 : ℝ)*x 0 + (5392306711/10000000000 : ℝ)*x 1 + (658295933/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149323713/10000000000 : ℝ)^2093 ≤ (6531917264341/50000000000000 : ℝ)^1581 := by
    have hnat : (2149323713 : ℕ)^2093*50000000000000^1581 ≤ 6531917264341^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149323713 10000000000 6531917264341 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392306711/10000000000 : ℝ)^2093 ≤ (11036997833897/25000000000000 : ℝ)^1581 := by
    have hnat : (5392306711 : ℕ)^2093*25000000000000^1581 ≤ 11036997833897^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392306711 10000000000 11036997833897 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658295933/1250000000 : ℝ)^2093 ≤ (42788174120561/100000000000000 : ℝ)^1581 := by
    have hnat : (658295933 : ℕ)^2093*100000000000000^1581 ≤ 42788174120561^1581*1250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658295933 1250000000 42788174120561 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149323713/10000000000 : ℝ), (5392306711/10000000000 : ℝ), (658295933/1250000000 : ℝ)] ![(6531917264341/50000000000000 : ℝ), (11036997833897/25000000000000 : ℝ), (42788174120561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149323713/10000000000 : ℝ)|^2093 ≤ (6531917264341/50000000000000 : ℝ)^1581
        have hw : |(-2149323713/10000000000 : ℝ)|=(2149323713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392306711/10000000000 : ℝ)|^2093 ≤ (11036997833897/25000000000000 : ℝ)^1581
        have hw : |(5392306711/10000000000 : ℝ)|=(5392306711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658295933/1250000000 : ℝ)|^2093 ≤ (42788174120561/100000000000000 : ℝ)^1581
        have hw : |(658295933/1250000000 : ℝ)|=(658295933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s10_1 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672298141/5000000000 : ℝ)*x 0 + (-2213191751/10000000000 : ℝ)*x 1 + (5266367739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672298141/5000000000 : ℝ)^2093 ≤ (21815809392973/50000000000000 : ℝ)^1581 := by
    have hnat : (2672298141 : ℕ)^2093*50000000000000^1581 ≤ 21815809392973^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672298141 5000000000 21815809392973 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213191751/10000000000 : ℝ)^2093 ≤ (33950510297/250000000000 : ℝ)^1581 := by
    have hnat : (2213191751 : ℕ)^2093*250000000000^1581 ≤ 33950510297^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213191751 10000000000 33950510297 250000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266367739/10000000000 : ℝ)^2093 ≤ (8557635415691/20000000000000 : ℝ)^1581 := by
    have hnat : (5266367739 : ℕ)^2093*20000000000000^1581 ≤ 8557635415691^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266367739 10000000000 8557635415691 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672298141/5000000000 : ℝ), (-2213191751/10000000000 : ℝ), (5266367739/10000000000 : ℝ)] ![(21815809392973/50000000000000 : ℝ), (33950510297/250000000000 : ℝ), (8557635415691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672298141/5000000000 : ℝ)|^2093 ≤ (21815809392973/50000000000000 : ℝ)^1581
        have hw : |(2672298141/5000000000 : ℝ)|=(2672298141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2213191751/10000000000 : ℝ)|^2093 ≤ (33950510297/250000000000 : ℝ)^1581
        have hw : |(-2213191751/10000000000 : ℝ)|=(2213191751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266367739/10000000000 : ℝ)|^2093 ≤ (8557635415691/20000000000000 : ℝ)^1581
        have hw : |(5266367739/10000000000 : ℝ)|=(5266367739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s10_2 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344596407/10000000000 : ℝ)*x 0 + (2633183803/5000000000 : ℝ)*x 1 + (-2213191761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344596407/10000000000 : ℝ)^2093 ≤ (21815810068439/50000000000000 : ℝ)^1581 := by
    have hnat : (5344596407 : ℕ)^2093*50000000000000^1581 ≤ 21815810068439^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344596407 10000000000 21815810068439 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633183803/5000000000 : ℝ)^2093 ≤ (4278817564791/10000000000000 : ℝ)^1581 := by
    have hnat : (2633183803 : ℕ)^2093*10000000000000^1581 ≤ 4278817564791^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633183803 5000000000 4278817564791 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2213191761/10000000000 : ℝ)^2093 ≤ (13580204200031/100000000000000 : ℝ)^1581 := by
    have hnat : (2213191761 : ℕ)^2093*100000000000000^1581 ≤ 13580204200031^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213191761 10000000000 13580204200031 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344596407/10000000000 : ℝ), (2633183803/5000000000 : ℝ), (-2213191761/10000000000 : ℝ)] ![(21815810068439/50000000000000 : ℝ), (4278817564791/10000000000000 : ℝ), (13580204200031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344596407/10000000000 : ℝ)|^2093 ≤ (21815810068439/50000000000000 : ℝ)^1581
        have hw : |(5344596407/10000000000 : ℝ)|=(5344596407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633183803/5000000000 : ℝ)|^2093 ≤ (4278817564791/10000000000000 : ℝ)^1581
        have hw : |(2633183803/5000000000 : ℝ)|=(2633183803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2213191761/10000000000 : ℝ)|^2093 ≤ (13580204200031/100000000000000 : ℝ)^1581
        have hw : |(-2213191761/10000000000 : ℝ)|=(2213191761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s10_3 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4359489509/10000000000 : ℝ)*x 0 + (1058776287/2500000000 : ℝ)*x 1 + (1121869089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359489509/10000000000 : ℝ)^2093 ≤ (33317194954981/100000000000000 : ℝ)^1581 := by
    have hnat : (4359489509 : ℕ)^2093*100000000000000^1581 ≤ 33317194954981^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359489509 10000000000 33317194954981 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058776287/2500000000 : ℝ)^2093 ≤ (8016149220963/25000000000000 : ℝ)^1581 := by
    have hnat : (1058776287 : ℕ)^2093*25000000000000^1581 ≤ 8016149220963^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058776287 2500000000 8016149220963 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121869089/2500000000 : ℝ)^2093 ≤ (34618208154671/100000000000000 : ℝ)^1581 := by
    have hnat : (1121869089 : ℕ)^2093*100000000000000^1581 ≤ 34618208154671^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121869089 2500000000 34618208154671 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359489509/10000000000 : ℝ), (1058776287/2500000000 : ℝ), (1121869089/2500000000 : ℝ)] ![(33317194954981/100000000000000 : ℝ), (8016149220963/25000000000000 : ℝ), (34618208154671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359489509/10000000000 : ℝ)|^2093 ≤ (33317194954981/100000000000000 : ℝ)^1581
        have hw : |(4359489509/10000000000 : ℝ)|=(4359489509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058776287/2500000000 : ℝ)|^2093 ≤ (8016149220963/25000000000000 : ℝ)^1581
        have hw : |(1058776287/2500000000 : ℝ)|=(1058776287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121869089/2500000000 : ℝ)|^2093 ≤ (34618208154671/100000000000000 : ℝ)^1581
        have hw : |(1121869089/2500000000 : ℝ)|=(1121869089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s10_4 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149328159/10000000000 : ℝ)*x 0 + (5266684327/10000000000 : ℝ)*x 1 + (1347997239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149328159/10000000000 : ℝ)^2093 ≤ (6531935151683/50000000000000 : ℝ)^1581 := by
    have hnat : (2149328159 : ℕ)^2093*50000000000000^1581 ≤ 6531935151683^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149328159 10000000000 6531935151683 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266684327/10000000000 : ℝ)^2093 ≤ (42791582325603/100000000000000 : ℝ)^1581 := by
    have hnat : (5266684327 : ℕ)^2093*100000000000000^1581 ≤ 42791582325603^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266684327 10000000000 42791582325603 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347997239/2500000000 : ℝ)^2093 ≤ (44144547344893/100000000000000 : ℝ)^1581 := by
    have hnat : (1347997239 : ℕ)^2093*100000000000000^1581 ≤ 44144547344893^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347997239 2500000000 44144547344893 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149328159/10000000000 : ℝ), (5266684327/10000000000 : ℝ), (1347997239/2500000000 : ℝ)] ![(6531935151683/50000000000000 : ℝ), (42791582325603/100000000000000 : ℝ), (44144547344893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149328159/10000000000 : ℝ)|^2093 ≤ (6531935151683/50000000000000 : ℝ)^1581
        have hw : |(-2149328159/10000000000 : ℝ)|=(2149328159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266684327/10000000000 : ℝ)|^2093 ≤ (42791582325603/100000000000000 : ℝ)^1581
        have hw : |(5266684327/10000000000 : ℝ)|=(5266684327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347997239/2500000000 : ℝ)|^2093 ≤ (44144547344893/100000000000000 : ℝ)^1581
        have hw : |(1347997239/2500000000 : ℝ)|=(1347997239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s10_5 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062520561/2000000000 : ℝ)*x 0 + (-2087570697/10000000000 : ℝ)*x 1 + (107839779/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062520561/2000000000 : ℝ)^2093 ≤ (43286186053353/100000000000000 : ℝ)^1581 := by
    have hnat : (1062520561 : ℕ)^2093*100000000000000^1581 ≤ 43286186053353^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062520561 2000000000 43286186053353 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087570697/10000000000 : ℝ)^2093 ≤ (6284633329087/50000000000000 : ℝ)^1581 := by
    have hnat : (2087570697 : ℕ)^2093*50000000000000^1581 ≤ 6284633329087^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087570697 10000000000 6284633329087 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107839779/200000000 : ℝ)^2093 ≤ (22072273639931/50000000000000 : ℝ)^1581 := by
    have hnat : (107839779 : ℕ)^2093*50000000000000^1581 ≤ 22072273639931^1581*200000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107839779 200000000 22072273639931 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062520561/2000000000 : ℝ), (-2087570697/10000000000 : ℝ), (107839779/200000000 : ℝ)] ![(43286186053353/100000000000000 : ℝ), (6284633329087/50000000000000 : ℝ), (22072273639931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062520561/2000000000 : ℝ)|^2093 ≤ (43286186053353/100000000000000 : ℝ)^1581
        have hw : |(1062520561/2000000000 : ℝ)|=(1062520561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2087570697/10000000000 : ℝ)|^2093 ≤ (6284633329087/50000000000000 : ℝ)^1581
        have hw : |(-2087570697/10000000000 : ℝ)|=(2087570697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107839779/200000000 : ℝ)|^2093 ≤ (22072273639931/50000000000000 : ℝ)^1581
        have hw : |(107839779/200000000 : ℝ)|=(107839779/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s10_6 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312602891/10000000000 : ℝ)*x 0 + (539198887/1000000000 : ℝ)*x 1 + (-2087570689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312602891/10000000000 : ℝ)^2093 ≤ (43286186980989/100000000000000 : ℝ)^1581 := by
    have hnat : (5312602891 : ℕ)^2093*100000000000000^1581 ≤ 43286186980989^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312602891 10000000000 43286186980989 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539198887/1000000000 : ℝ)^2093 ≤ (4414454641279/10000000000000 : ℝ)^1581 := by
    have hnat : (539198887 : ℕ)^2093*10000000000000^1581 ≤ 4414454641279^1581*1000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539198887 1000000000 4414454641279 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087570689/10000000000 : ℝ)^2093 ≤ (12569266594407/100000000000000 : ℝ)^1581 := by
    have hnat : (2087570689 : ℕ)^2093*100000000000000^1581 ≤ 12569266594407^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087570689 10000000000 12569266594407 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312602891/10000000000 : ℝ), (539198887/1000000000 : ℝ), (-2087570689/10000000000 : ℝ)] ![(43286186980989/100000000000000 : ℝ), (4414454641279/10000000000000 : ℝ), (12569266594407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312602891/10000000000 : ℝ)|^2093 ≤ (43286186980989/100000000000000 : ℝ)^1581
        have hw : |(5312602891/10000000000 : ℝ)|=(5312602891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539198887/1000000000 : ℝ)|^2093 ≤ (4414454641279/10000000000000 : ℝ)^1581
        have hw : |(539198887/1000000000 : ℝ)|=(539198887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087570689/10000000000 : ℝ)|^2093 ≤ (12569266594407/100000000000000 : ℝ)^1581
        have hw : |(-2087570689/10000000000 : ℝ)|=(2087570689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s10_7 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-7291037/2500000000 : ℝ)*x 0 + (37012161/62500000 : ℝ)*x 1 + (2960979901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7291037/2500000000 : ℝ)^2093 ≤ (22020223649/50000000000000 : ℝ)^1581 := by
    have hnat : (7291037 : ℕ)^2093*50000000000000^1581 ≤ 22020223649^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7291037 2500000000 22020223649 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37012161/62500000 : ℝ)^2093 ≤ (24988950664027/50000000000000 : ℝ)^1581 := by
    have hnat : (37012161 : ℕ)^2093*50000000000000^1581 ≤ 24988950664027^1581*62500000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37012161 62500000 24988950664027 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2960979901/5000000000 : ℝ)^2093 ≤ (4997805821257/10000000000000 : ℝ)^1581 := by
    have hnat : (2960979901 : ℕ)^2093*10000000000000^1581 ≤ 4997805821257^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2960979901 5000000000 4997805821257 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7291037/2500000000 : ℝ), (37012161/62500000 : ℝ), (2960979901/5000000000 : ℝ)] ![(22020223649/50000000000000 : ℝ), (24988950664027/50000000000000 : ℝ), (4997805821257/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7291037/2500000000 : ℝ)|^2093 ≤ (22020223649/50000000000000 : ℝ)^1581
        have hw : |(-7291037/2500000000 : ℝ)|=(7291037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(37012161/62500000 : ℝ)|^2093 ≤ (24988950664027/50000000000000 : ℝ)^1581
        have hw : |(37012161/62500000 : ℝ)|=(37012161/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2960979901/5000000000 : ℝ)|^2093 ≤ (4997805821257/10000000000000 : ℝ)^1581
        have hw : |(2960979901/5000000000 : ℝ)|=(2960979901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1179_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5701/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11401/100000 : ℝ) ^ (8371/2048 : ℝ) ≤ (2794965049692037/20000000000000000000 : ℝ) := by
    have hpowers : (11401/100000 : ℝ)^8371 ≤ (2794965049692037/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11401 : ℕ)^8371*20000000000000000000^2048 ≤ 2794965049692037^2048*100000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11401 100000 2794965049692037 20000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11401/100000 : ℝ)) (X := (2794965049692037/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14069/100000 : ℝ) ^ (8371/2048 : ℝ) ≤ (16503616867015037/50000000000000000000 : ℝ) := by
    have hpowers : (14069/100000 : ℝ)^8371 ≤ (16503616867015037/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14069 : ℕ)^8371*50000000000000000000^2048 ≤ 16503616867015037^2048*100000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14069 100000 16503616867015037 50000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14069/100000 : ℝ)) (X := (16503616867015037/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002794965049692037/10000000000000000000 : ℝ) ≤ (5000341863833219/5000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (10002794965049692037/10000000000000000000 : ℝ)^2048 ≤ (5000341863833219/5000000000000000 : ℝ)^8371 := by
      have hnat : (10002794965049692037 : ℕ)^2048*5000000000000000^8371 ≤ 5000341863833219^8371*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002794965049692037 10000000000000000000 5000341863833219 5000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000341863833219/5000000000000000 : ℝ)) (X := (10002794965049692037/10000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046982058982490259/100000000000000000000 : ℝ) ≤ (5000574615867197/5000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (100046982058982490259/100000000000000000000 : ℝ)^2048 ≤ (5000574615867197/5000000000000000 : ℝ)^8371 := by
      have hnat : (100046982058982490259 : ℕ)^2048*5000000000000000^8371 ≤ 5000574615867197^8371*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046982058982490259 100000000000000000000 5000574615867197 5000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000574615867197/5000000000000000 : ℝ)) (X := (100046982058982490259/100000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016503616867015037/25000000000000000000 : ℝ) ≤ (200032294716047/200000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (25016503616867015037/25000000000000000000 : ℝ)^2048 ≤ (200032294716047/200000000000000 : ℝ)^8371 := by
      have hnat : (25016503616867015037 : ℕ)^2048*200000000000000^8371 ≤ 200032294716047^8371*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016503616867015037 25000000000000000000 200032294716047 200000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200032294716047/200000000000000 : ℝ)) (X := (25016503616867015037/25000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2794965049692037/20000000000000000000 : ℝ) ≤ ((833475305051766371/833750000000000000 : ℝ)+2*(116376016989/66700000000000 : ℝ)*(11401/100000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (833475305051766371/833750000000000000 : ℝ)+2*(116376016989/66700000000000 : ℝ)*(11401/100000 : ℝ)=(5000341863833219/5000000000000000 : ℝ) by norm_num, show 1+2*(2794965049692037/20000000000000000000 : ℝ)=(10002794965049692037/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16503616867015037/50000000000000000000 : ℝ)+(2794965049692037/20000000000000000000 : ℝ) ≤ ((833475305051766371/833750000000000000 : ℝ)+(116376016989/66700000000000 : ℝ)*((14069/100000 : ℝ)+(11401/100000 : ℝ)))^(8371/2048 : ℝ) := by
    rw [show (833475305051766371/833750000000000000 : ℝ)+(116376016989/66700000000000 : ℝ)*((14069/100000 : ℝ)+(11401/100000 : ℝ))=(5000574615867197/5000000000000000 : ℝ) by norm_num, show 1+(16503616867015037/50000000000000000000 : ℝ)+(2794965049692037/20000000000000000000 : ℝ)=(100046982058982490259/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16503616867015037/50000000000000000000 : ℝ) ≤ ((833475305051766371/833750000000000000 : ℝ)+2*(116376016989/66700000000000 : ℝ)*(14069/100000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (833475305051766371/833750000000000000 : ℝ)+2*(116376016989/66700000000000 : ℝ)*(14069/100000 : ℝ)=(200032294716047/200000000000000 : ℝ) by norm_num, show 1+2*(16503616867015037/50000000000000000000 : ℝ)=(25016503616867015037/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (833475305051766371/833750000000000000 : ℝ)*(X 1 0+X 2 0)+(116376016989/66700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (833475305051766371/833750000000000000 : ℝ)) (alpha := (116376016989/66700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (833475305051766371/833750000000000000 : ℝ)*(X 0 1+X 2 1)+(116376016989/66700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (833475305051766371/833750000000000000 : ℝ)) (alpha := (116376016989/66700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (833475305051766371/833750000000000000 : ℝ)*(X 0 2+X 1 2)+(116376016989/66700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (833475305051766371/833750000000000000 : ℝ)) (alpha := (116376016989/66700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2149323713/10000000000 : ℝ)*X 0 0+(5392306711/10000000000 : ℝ)*X 0 1+(658295933/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s10_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672298141/5000000000 : ℝ)*X 1 0+(-2213191751/10000000000 : ℝ)*X 1 1+(5266367739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s10_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344596407/10000000000 : ℝ)*X 2 0+(2633183803/5000000000 : ℝ)*X 2 1+(-2213191761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s10_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359489509/10000000000 : ℝ)*X 0 0+(1058776287/2500000000 : ℝ)*X 0 1+(1121869089/2500000000 : ℝ)*X 0 2+(4359489509/10000000000 : ℝ)*X 1 0+(1058776287/2500000000 : ℝ)*X 1 1+(1121869089/2500000000 : ℝ)*X 1 2+(4359489509/10000000000 : ℝ)*X 2 0+(1058776287/2500000000 : ℝ)*X 2 1+(1121869089/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s10_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2149328159/10000000000 : ℝ)*X 0 0+(5266684327/10000000000 : ℝ)*X 0 1+(1347997239/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s10_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062520561/2000000000 : ℝ)*X 1 0+(-2087570697/10000000000 : ℝ)*X 1 1+(107839779/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s10_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312602891/10000000000 : ℝ)*X 2 0+(539198887/1000000000 : ℝ)*X 2 1+(-2087570689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s10_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((-7291037/2500000000 : ℝ)*X 0 0+(37012161/62500000 : ℝ)*X 0 1+(2960979901/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s10_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2121005273936177231556873/906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (489155041/100000000000000 : ℝ)*(lower2) + (369755021/100000000000000 : ℝ)*(lower4) + (291352739/100000000000000 : ℝ)*(lower5) + (2975692598253661/50000000000000 : ℝ)*(major0) + (2975692598253661/50000000000000 : ℝ)*(major1) + (2975692598253661/50000000000000 : ℝ)*(major2) + (794035064977401/10000000000000 : ℝ)*(sp0) + (1588069460289951/20000000000000 : ℝ)*(sp1) + (7940353598212681/100000000000000 : ℝ)*(sp2) + (1981204521718023/50000000000000 : ℝ)*(sp3) + (5707903497/100000000000000 : ℝ)*(sp4) + (436566089/3125000000000 : ℝ)*(sp5) + (3836675961/50000000000000 : ℝ)*(sp6) + (2456943549/50000000000000 : ℝ)*(sp7) + (1981204521718023/50000000000000 : ℝ)*(f.failure) + (7940361271564603/100000000000000 : ℝ)*(f.sum) + (130001585919/145000000000000000000000000 : ℝ)*base66 + (755866973558307/62500000000000000000000000000 : ℝ)*base68 + (484248900245807/62500000000000000000000000000 : ℝ)*base70 + (472564413995807/62500000000000000000000000000 : ℝ)*base72 + (272054749469/145000000000000000000000000 : ℝ)*base74 + (448708848808307/62500000000000000000000000000 : ℝ)*base76 + (443332171433307/62500000000000000000000000000 : ℝ)*base78 + (392075893370807/62500000000000000000000000000 : ℝ)*base80 + (163624928319/145000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base83 + (3638459/2500000000000000000000 : ℝ)*base90 + (3638459/2500000000000000000000 : ℝ)*base92 + (3638459/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1179_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1179_s10 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1179_box_0 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-505910659/2500000000 : ℝ)*x 0 + (1075154553/2000000000 : ℝ)*x 1 + (2687886429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505910659/2500000000 : ℝ)^2093 ≤ (12062248329393/100000000000000 : ℝ)^1581 := by
    have hnat : (505910659 : ℕ)^2093*100000000000000^1581 ≤ 12062248329393^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505910659 2500000000 12062248329393 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075154553/2000000000 : ℝ)^2093 ≤ (43968875324123/100000000000000 : ℝ)^1581 := by
    have hnat : (1075154553 : ℕ)^2093*100000000000000^1581 ≤ 43968875324123^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075154553 2000000000 43968875324123 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687886429/5000000000 : ℝ)^2093 ≤ (5496109541389/12500000000000 : ℝ)^1581 := by
    have hnat : (2687886429 : ℕ)^2093*12500000000000^1581 ≤ 5496109541389^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687886429 5000000000 5496109541389 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505910659/2500000000 : ℝ), (1075154553/2000000000 : ℝ), (2687886429/5000000000 : ℝ)] ![(12062248329393/100000000000000 : ℝ), (43968875324123/100000000000000 : ℝ), (5496109541389/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505910659/2500000000 : ℝ)|^2093 ≤ (12062248329393/100000000000000 : ℝ)^1581
        have hw : |(-505910659/2500000000 : ℝ)|=(505910659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075154553/2000000000 : ℝ)|^2093 ≤ (43968875324123/100000000000000 : ℝ)^1581
        have hw : |(1075154553/2000000000 : ℝ)|=(1075154553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687886429/5000000000 : ℝ)|^2093 ≤ (5496109541389/12500000000000 : ℝ)^1581
        have hw : |(2687886429/5000000000 : ℝ)|=(2687886429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_1 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5296314641/10000000000 : ℝ)*x 0 + (-532872993/2500000000 : ℝ)*x 1 + (5375772609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296314641/10000000000 : ℝ)^2093 ≤ (21555290772917/50000000000000 : ℝ)^1581 := by
    have hnat : (5296314641 : ℕ)^2093*50000000000000^1581 ≤ 21555290772917^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296314641 10000000000 21555290772917 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532872993/2500000000 : ℝ)^2093 ≤ (1615068101083/12500000000000 : ℝ)^1581 := by
    have hnat : (532872993 : ℕ)^2093*12500000000000^1581 ≤ 1615068101083^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532872993 2500000000 1615068101083 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375772609/10000000000 : ℝ)^2093 ≤ (2198443681749/5000000000000 : ℝ)^1581 := by
    have hnat : (5375772609 : ℕ)^2093*5000000000000^1581 ≤ 2198443681749^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375772609 10000000000 2198443681749 5000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296314641/10000000000 : ℝ), (-532872993/2500000000 : ℝ), (5375772609/10000000000 : ℝ)] ![(21555290772917/50000000000000 : ℝ), (1615068101083/12500000000000 : ℝ), (2198443681749/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296314641/10000000000 : ℝ)|^2093 ≤ (21555290772917/50000000000000 : ℝ)^1581
        have hw : |(5296314641/10000000000 : ℝ)|=(5296314641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532872993/2500000000 : ℝ)|^2093 ≤ (1615068101083/12500000000000 : ℝ)^1581
        have hw : |(-532872993/2500000000 : ℝ)|=(532872993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375772609/10000000000 : ℝ)|^2093 ≤ (2198443681749/5000000000000 : ℝ)^1581
        have hw : |(5375772609/10000000000 : ℝ)|=(5375772609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_2 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2648157683/5000000000 : ℝ)*x 0 + (1075154417/2000000000 : ℝ)*x 1 + (-266436463/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648157683/5000000000 : ℝ)^2093 ≤ (10777647339563/25000000000000 : ℝ)^1581 := by
    have hnat : (2648157683 : ℕ)^2093*25000000000000^1581 ≤ 10777647339563^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648157683 5000000000 10777647339563 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075154417/2000000000 : ℝ)^2093 ≤ (5496108495149/12500000000000 : ℝ)^1581 := by
    have hnat : (1075154417 : ℕ)^2093*12500000000000^1581 ≤ 5496108495149^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075154417 2000000000 5496108495149 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266436463/1250000000 : ℝ)^2093 ≤ (403766958063/3125000000000 : ℝ)^1581 := by
    have hnat : (266436463 : ℕ)^2093*3125000000000^1581 ≤ 403766958063^1581*1250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266436463 1250000000 403766958063 3125000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648157683/5000000000 : ℝ), (1075154417/2000000000 : ℝ), (-266436463/1250000000 : ℝ)] ![(10777647339563/25000000000000 : ℝ), (5496108495149/12500000000000 : ℝ), (403766958063/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648157683/5000000000 : ℝ)|^2093 ≤ (10777647339563/25000000000000 : ℝ)^1581
        have hw : |(2648157683/5000000000 : ℝ)|=(2648157683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075154417/2000000000 : ℝ)|^2093 ≤ (5496108495149/12500000000000 : ℝ)^1581
        have hw : |(1075154417/2000000000 : ℝ)|=(1075154417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266436463/1250000000 : ℝ)|^2093 ≤ (403766958063/3125000000000 : ℝ)^1581
        have hw : |(-266436463/1250000000 : ℝ)|=(266436463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_3 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1116659227/2500000000 : ℝ)*x 0 + (861599581/2000000000 : ℝ)*x 1 + (861599493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1116659227/2500000000 : ℝ)^2093 ≤ (8601385430591/25000000000000 : ℝ)^1581 := by
    have hnat : (1116659227 : ℕ)^2093*25000000000000^1581 ≤ 8601385430591^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116659227 2500000000 8601385430591 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861599581/2000000000 : ℝ)^2093 ≤ (16398615673807/50000000000000 : ℝ)^1581 := by
    have hnat : (861599581 : ℕ)^2093*50000000000000^1581 ≤ 16398615673807^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861599581 2000000000 16398615673807 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (861599493/2000000000 : ℝ)^2093 ≤ (32797226913041/100000000000000 : ℝ)^1581 := by
    have hnat : (861599493 : ℕ)^2093*100000000000000^1581 ≤ 32797226913041^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861599493 2000000000 32797226913041 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1116659227/2500000000 : ℝ), (861599581/2000000000 : ℝ), (861599493/2000000000 : ℝ)] ![(8601385430591/25000000000000 : ℝ), (16398615673807/50000000000000 : ℝ), (32797226913041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1116659227/2500000000 : ℝ)|^2093 ≤ (8601385430591/25000000000000 : ℝ)^1581
        have hw : |(1116659227/2500000000 : ℝ)|=(1116659227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(861599581/2000000000 : ℝ)|^2093 ≤ (16398615673807/50000000000000 : ℝ)^1581
        have hw : |(861599581/2000000000 : ℝ)|=(861599581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(861599493/2000000000 : ℝ)|^2093 ≤ (32797226913041/100000000000000 : ℝ)^1581
        have hw : |(861599493/2000000000 : ℝ)|=(861599493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_4 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2276379879/10000000000 : ℝ)*x 0 + (5281598559/10000000000 : ℝ)*x 1 + (2640799231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2276379879/10000000000 : ℝ)^2093 ≤ (14095848765551/100000000000000 : ℝ)^1581 := by
    have hnat : (2276379879 : ℕ)^2093*100000000000000^1581 ≤ 14095848765551^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276379879 10000000000 14095848765551 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281598559/10000000000 : ℝ)^2093 ≤ (42952076131777/100000000000000 : ℝ)^1581 := by
    have hnat : (5281598559 : ℕ)^2093*100000000000000^1581 ≤ 42952076131777^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281598559 10000000000 42952076131777 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640799231/5000000000 : ℝ)^2093 ≤ (4295207508747/10000000000000 : ℝ)^1581 := by
    have hnat : (2640799231 : ℕ)^2093*10000000000000^1581 ≤ 4295207508747^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640799231 5000000000 4295207508747 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2276379879/10000000000 : ℝ), (5281598559/10000000000 : ℝ), (2640799231/5000000000 : ℝ)] ![(14095848765551/100000000000000 : ℝ), (42952076131777/100000000000000 : ℝ), (4295207508747/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2276379879/10000000000 : ℝ)|^2093 ≤ (14095848765551/100000000000000 : ℝ)^1581
        have hw : |(-2276379879/10000000000 : ℝ)|=(2276379879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281598559/10000000000 : ℝ)|^2093 ≤ (42952076131777/100000000000000 : ℝ)^1581
        have hw : |(5281598559/10000000000 : ℝ)|=(5281598559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640799231/5000000000 : ℝ)|^2093 ≤ (4295207508747/10000000000000 : ℝ)^1581
        have hw : |(2640799231/5000000000 : ℝ)|=(2640799231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_5 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2681396839/5000000000 : ℝ)*x 0 + (-542161267/2500000000 : ℝ)*x 1 + (82524977/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681396839/5000000000 : ℝ)^2093 ≤ (4382839482327/10000000000000 : ℝ)^1581 := by
    have hnat : (2681396839 : ℕ)^2093*10000000000000^1581 ≤ 4382839482327^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681396839 5000000000 4382839482327 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542161267/2500000000 : ℝ)^2093 ≤ (13219529364183/100000000000000 : ℝ)^1581 := by
    have hnat : (542161267 : ℕ)^2093*100000000000000^1581 ≤ 13219529364183^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542161267 2500000000 13219529364183 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82524977/156250000 : ℝ)^2093 ≤ (42952075798029/100000000000000 : ℝ)^1581 := by
    have hnat : (82524977 : ℕ)^2093*100000000000000^1581 ≤ 42952075798029^1581*156250000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82524977 156250000 42952075798029 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681396839/5000000000 : ℝ), (-542161267/2500000000 : ℝ), (82524977/156250000 : ℝ)] ![(4382839482327/10000000000000 : ℝ), (13219529364183/100000000000000 : ℝ), (42952075798029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681396839/5000000000 : ℝ)|^2093 ≤ (4382839482327/10000000000000 : ℝ)^1581
        have hw : |(2681396839/5000000000 : ℝ)|=(2681396839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-542161267/2500000000 : ℝ)|^2093 ≤ (13219529364183/100000000000000 : ℝ)^1581
        have hw : |(-542161267/2500000000 : ℝ)|=(542161267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82524977/156250000 : ℝ)|^2093 ≤ (42952075798029/100000000000000 : ℝ)^1581
        have hw : |(82524977/156250000 : ℝ)|=(82524977/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_6 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362793861/10000000000 : ℝ)*x 0 + (1320399629/2500000000 : ℝ)*x 1 + (-2168644839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362793861/10000000000 : ℝ)^2093 ≤ (21914198401607/50000000000000 : ℝ)^1581 := by
    have hnat : (5362793861 : ℕ)^2093*50000000000000^1581 ≤ 21914198401607^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362793861 10000000000 21914198401607 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320399629/2500000000 : ℝ)^2093 ≤ (42952075668837/100000000000000 : ℝ)^1581 := by
    have hnat : (1320399629 : ℕ)^2093*100000000000000^1581 ≤ 42952075668837^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320399629 2500000000 42952075668837 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168644839/10000000000 : ℝ)^2093 ≤ (1321952751619/10000000000000 : ℝ)^1581 := by
    have hnat : (2168644839 : ℕ)^2093*10000000000000^1581 ≤ 1321952751619^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168644839 10000000000 1321952751619 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362793861/10000000000 : ℝ), (1320399629/2500000000 : ℝ), (-2168644839/10000000000 : ℝ)] ![(21914198401607/50000000000000 : ℝ), (42952075668837/100000000000000 : ℝ), (1321952751619/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362793861/10000000000 : ℝ)|^2093 ≤ (21914198401607/50000000000000 : ℝ)^1581
        have hw : |(5362793861/10000000000 : ℝ)|=(5362793861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320399629/2500000000 : ℝ)|^2093 ≤ (42952075668837/100000000000000 : ℝ)^1581
        have hw : |(1320399629/2500000000 : ℝ)|=(1320399629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2168644839/10000000000 : ℝ)|^2093 ≤ (1321952751619/10000000000000 : ℝ)^1581
        have hw : |(-2168644839/10000000000 : ℝ)|=(2168644839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_7 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4251964353/10000000000 : ℝ)*x 0 + (2207656669/5000000000 : ℝ)*x 1 + (2207656741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251964353/10000000000 : ℝ)^2093 ≤ (32233685993121/100000000000000 : ℝ)^1581 := by
    have hnat : (4251964353 : ℕ)^2093*100000000000000^1581 ≤ 32233685993121^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251964353 10000000000 32233685993121 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207656669/5000000000 : ℝ)^2093 ≤ (33883156269037/100000000000000 : ℝ)^1581 := by
    have hnat : (2207656669 : ℕ)^2093*100000000000000^1581 ≤ 33883156269037^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207656669 5000000000 33883156269037 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207656741/5000000000 : ℝ)^2093 ≤ (33883157731963/100000000000000 : ℝ)^1581 := by
    have hnat : (2207656741 : ℕ)^2093*100000000000000^1581 ≤ 33883157731963^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207656741 5000000000 33883157731963 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251964353/10000000000 : ℝ), (2207656669/5000000000 : ℝ), (2207656741/5000000000 : ℝ)] ![(32233685993121/100000000000000 : ℝ), (33883156269037/100000000000000 : ℝ), (33883157731963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251964353/10000000000 : ℝ)|^2093 ≤ (32233685993121/100000000000000 : ℝ)^1581
        have hw : |(4251964353/10000000000 : ℝ)|=(4251964353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2207656669/5000000000 : ℝ)|^2093 ≤ (33883156269037/100000000000000 : ℝ)^1581
        have hw : |(2207656669/5000000000 : ℝ)|=(2207656669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2207656741/5000000000 : ℝ)|^2093 ≤ (33883157731963/100000000000000 : ℝ)^1581
        have hw : |(2207656741/5000000000 : ℝ)|=(2207656741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_8 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-17787897/80000000 : ℝ)*x 0 + (208699209/400000000 : ℝ)*x 1 + (538538323/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17787897/80000000 : ℝ)^2093 ≤ (6831948970521/50000000000000 : ℝ)^1581 := by
    have hnat : (17787897 : ℕ)^2093*50000000000000^1581 ≤ 6831948970521^1581*80000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17787897 80000000 6831948970521 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208699209/400000000 : ℝ)^2093 ≤ (42263136038267/100000000000000 : ℝ)^1581 := by
    have hnat : (208699209 : ℕ)^2093*100000000000000^1581 ≤ 42263136038267^1581*400000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208699209 400000000 42263136038267 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538538323/1000000000 : ℝ)^2093 ≤ (5509120751029/12500000000000 : ℝ)^1581 := by
    have hnat : (538538323 : ℕ)^2093*12500000000000^1581 ≤ 5509120751029^1581*1000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538538323 1000000000 5509120751029 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17787897/80000000 : ℝ), (208699209/400000000 : ℝ), (538538323/1000000000 : ℝ)] ![(6831948970521/50000000000000 : ℝ), (42263136038267/100000000000000 : ℝ), (5509120751029/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17787897/80000000 : ℝ)|^2093 ≤ (6831948970521/50000000000000 : ℝ)^1581
        have hw : |(-17787897/80000000 : ℝ)|=(17787897/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208699209/400000000 : ℝ)|^2093 ≤ (42263136038267/100000000000000 : ℝ)^1581
        have hw : |(208699209/400000000 : ℝ)|=(208699209/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538538323/1000000000 : ℝ)|^2093 ≤ (5509120751029/12500000000000 : ℝ)^1581
        have hw : |(538538323/1000000000 : ℝ)|=(538538323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_9 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289527893/10000000000 : ℝ)*x 0 + (-66488483/312500000 : ℝ)*x 1 + (5385382817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289527893/10000000000 : ℝ)^2093 ≤ (10759366108049/25000000000000 : ℝ)^1581 := by
    have hnat : (5289527893 : ℕ)^2093*25000000000000^1581 ≤ 10759366108049^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289527893 10000000000 10759366108049 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66488483/312500000 : ℝ)^2093 ≤ (128895740101/1000000000000 : ℝ)^1581 := by
    have hnat : (66488483 : ℕ)^2093*1000000000000^1581 ≤ 128895740101^1581*312500000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66488483 312500000 128895740101 1000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385382817/10000000000 : ℝ)^2093 ≤ (44072961533747/100000000000000 : ℝ)^1581 := by
    have hnat : (5385382817 : ℕ)^2093*100000000000000^1581 ≤ 44072961533747^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385382817 10000000000 44072961533747 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289527893/10000000000 : ℝ), (-66488483/312500000 : ℝ), (5385382817/10000000000 : ℝ)] ![(10759366108049/25000000000000 : ℝ), (128895740101/1000000000000 : ℝ), (44072961533747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289527893/10000000000 : ℝ)|^2093 ≤ (10759366108049/25000000000000 : ℝ)^1581
        have hw : |(5289527893/10000000000 : ℝ)|=(5289527893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66488483/312500000 : ℝ)|^2093 ≤ (128895740101/1000000000000 : ℝ)^1581
        have hw : |(-66488483/312500000 : ℝ)|=(66488483/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385382817/10000000000 : ℝ)|^2093 ≤ (44072961533747/100000000000000 : ℝ)^1581
        have hw : |(5385382817/10000000000 : ℝ)|=(5385382817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_10 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (165297743/312500000 : ℝ)*x 0 + (2692691201/5000000000 : ℝ)*x 1 + (-1063816087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165297743/312500000 : ℝ)^2093 ≤ (43037463171957/100000000000000 : ℝ)^1581 := by
    have hnat : (165297743 : ℕ)^2093*100000000000000^1581 ≤ 43037463171957^1581*312500000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165297743 312500000 43037463171957 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692691201/5000000000 : ℝ)^2093 ≤ (22036478518797/50000000000000 : ℝ)^1581 := by
    have hnat : (2692691201 : ℕ)^2093*50000000000000^1581 ≤ 22036478518797^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692691201 5000000000 22036478518797 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063816087/5000000000 : ℝ)^2093 ≤ (12889579768529/100000000000000 : ℝ)^1581 := by
    have hnat : (1063816087 : ℕ)^2093*100000000000000^1581 ≤ 12889579768529^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063816087 5000000000 12889579768529 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165297743/312500000 : ℝ), (2692691201/5000000000 : ℝ), (-1063816087/5000000000 : ℝ)] ![(43037463171957/100000000000000 : ℝ), (22036478518797/50000000000000 : ℝ), (12889579768529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165297743/312500000 : ℝ)|^2093 ≤ (43037463171957/100000000000000 : ℝ)^1581
        have hw : |(165297743/312500000 : ℝ)|=(165297743/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692691201/5000000000 : ℝ)|^2093 ≤ (22036478518797/50000000000000 : ℝ)^1581
        have hw : |(2692691201/5000000000 : ℝ)|=(2692691201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1063816087/5000000000 : ℝ)|^2093 ≤ (12889579768529/100000000000000 : ℝ)^1581
        have hw : |(-1063816087/5000000000 : ℝ)|=(1063816087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_11 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4488271227/10000000000 : ℝ)*x 0 + (537130003/1250000000 : ℝ)*x 1 + (4297039997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4488271227/10000000000 : ℝ)^2093 ≤ (17313163075757/50000000000000 : ℝ)^1581 := by
    have hnat : (4488271227 : ℕ)^2093*50000000000000^1581 ≤ 17313163075757^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488271227 10000000000 17313163075757 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537130003/1250000000 : ℝ)^2093 ≤ (16343418526849/50000000000000 : ℝ)^1581 := by
    have hnat : (537130003 : ℕ)^2093*50000000000000^1581 ≤ 16343418526849^1581*1250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537130003 1250000000 16343418526849 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4297039997/10000000000 : ℝ)^2093 ≤ (32686836781801/100000000000000 : ℝ)^1581 := by
    have hnat : (4297039997 : ℕ)^2093*100000000000000^1581 ≤ 32686836781801^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297039997 10000000000 32686836781801 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4488271227/10000000000 : ℝ), (537130003/1250000000 : ℝ), (4297039997/10000000000 : ℝ)] ![(17313163075757/50000000000000 : ℝ), (16343418526849/50000000000000 : ℝ), (32686836781801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4488271227/10000000000 : ℝ)|^2093 ≤ (17313163075757/50000000000000 : ℝ)^1581
        have hw : |(4488271227/10000000000 : ℝ)|=(4488271227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537130003/1250000000 : ℝ)|^2093 ≤ (16343418526849/50000000000000 : ℝ)^1581
        have hw : |(537130003/1250000000 : ℝ)|=(537130003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4297039997/10000000000 : ℝ)|^2093 ≤ (32686836781801/100000000000000 : ℝ)^1581
        have hw : |(4297039997/10000000000 : ℝ)|=(4297039997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_12 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2076832639/10000000000 : ℝ)*x 0 + (679829941/1250000000 : ℝ)*x 1 + (5273543973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2076832639/10000000000 : ℝ)^2093 ≤ (2496749258207/20000000000000 : ℝ)^1581 := by
    have hnat : (2076832639 : ℕ)^2093*20000000000000^1581 ≤ 2496749258207^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076832639 10000000000 2496749258207 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679829941/1250000000 : ℝ)^2093 ≤ (22325436081253/50000000000000 : ℝ)^1581 := by
    have hnat : (679829941 : ℕ)^2093*50000000000000^1581 ≤ 22325436081253^1581*1250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679829941 1250000000 22325436081253 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273543973/10000000000 : ℝ)^2093 ≤ (42865381529193/100000000000000 : ℝ)^1581 := by
    have hnat : (5273543973 : ℕ)^2093*100000000000000^1581 ≤ 42865381529193^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273543973 10000000000 42865381529193 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2076832639/10000000000 : ℝ), (679829941/1250000000 : ℝ), (5273543973/10000000000 : ℝ)] ![(2496749258207/20000000000000 : ℝ), (22325436081253/50000000000000 : ℝ), (42865381529193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2076832639/10000000000 : ℝ)|^2093 ≤ (2496749258207/20000000000000 : ℝ)^1581
        have hw : |(-2076832639/10000000000 : ℝ)|=(2076832639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679829941/1250000000 : ℝ)|^2093 ≤ (22325436081253/50000000000000 : ℝ)^1581
        have hw : |(679829941/1250000000 : ℝ)|=(679829941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273543973/10000000000 : ℝ)|^2093 ≤ (42865381529193/100000000000000 : ℝ)^1581
        have hw : |(5273543973/10000000000 : ℝ)|=(5273543973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_13 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368476983/10000000000 : ℝ)*x 0 + (-542941599/2500000000 : ℝ)*x 1 + (1318385981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368476983/10000000000 : ℝ)^2093 ≤ (43889895132481/100000000000000 : ℝ)^1581 := by
    have hnat : (5368476983 : ℕ)^2093*100000000000000^1581 ≤ 43889895132481^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368476983 10000000000 43889895132481 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542941599/2500000000 : ℝ)^2093 ≤ (13244723847227/100000000000000 : ℝ)^1581 := by
    have hnat : (542941599 : ℕ)^2093*100000000000000^1581 ≤ 13244723847227^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542941599 2500000000 13244723847227 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318385981/2500000000 : ℝ)^2093 ≤ (21432690500959/50000000000000 : ℝ)^1581 := by
    have hnat : (1318385981 : ℕ)^2093*50000000000000^1581 ≤ 21432690500959^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318385981 2500000000 21432690500959 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368476983/10000000000 : ℝ), (-542941599/2500000000 : ℝ), (1318385981/2500000000 : ℝ)] ![(43889895132481/100000000000000 : ℝ), (13244723847227/100000000000000 : ℝ), (21432690500959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368476983/10000000000 : ℝ)|^2093 ≤ (43889895132481/100000000000000 : ℝ)^1581
        have hw : |(5368476983/10000000000 : ℝ)|=(5368476983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-542941599/2500000000 : ℝ)|^2093 ≤ (13244723847227/100000000000000 : ℝ)^1581
        have hw : |(-542941599/2500000000 : ℝ)|=(542941599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318385981/2500000000 : ℝ)|^2093 ≤ (21432690500959/50000000000000 : ℝ)^1581
        have hw : |(1318385981/2500000000 : ℝ)|=(1318385981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_14 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368476957/10000000000 : ℝ)*x 0 + (2636772369/5000000000 : ℝ)*x 1 + (-1085882673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368476957/10000000000 : ℝ)^2093 ≤ (43889894851081/100000000000000 : ℝ)^1581 := by
    have hnat : (5368476957 : ℕ)^2093*100000000000000^1581 ≤ 43889894851081^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368476957 10000000000 43889894851081 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636772369/5000000000 : ℝ)^2093 ≤ (42865389761147/100000000000000 : ℝ)^1581 := by
    have hnat : (2636772369 : ℕ)^2093*100000000000000^1581 ≤ 42865389761147^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636772369 5000000000 42865389761147 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085882673/5000000000 : ℝ)^2093 ≤ (13244715369949/100000000000000 : ℝ)^1581 := by
    have hnat : (1085882673 : ℕ)^2093*100000000000000^1581 ≤ 13244715369949^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085882673 5000000000 13244715369949 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368476957/10000000000 : ℝ), (2636772369/5000000000 : ℝ), (-1085882673/5000000000 : ℝ)] ![(43889894851081/100000000000000 : ℝ), (42865389761147/100000000000000 : ℝ), (13244715369949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368476957/10000000000 : ℝ)|^2093 ≤ (43889894851081/100000000000000 : ℝ)^1581
        have hw : |(5368476957/10000000000 : ℝ)|=(5368476957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636772369/5000000000 : ℝ)|^2093 ≤ (42865389761147/100000000000000 : ℝ)^1581
        have hw : |(2636772369/5000000000 : ℝ)|=(2636772369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1085882673/5000000000 : ℝ)|^2093 ≤ (13244715369949/100000000000000 : ℝ)^1581
        have hw : |(-1085882673/5000000000 : ℝ)|=(1085882673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_box_15 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (423337307/1000000000 : ℝ)*x 0 + (4424486649/10000000000 : ℝ)*x 1 + (2212243341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423337307/1000000000 : ℝ)^2093 ≤ (1281889494691/4000000000000 : ℝ)^1581 := by
    have hnat : (423337307 : ℕ)^2093*4000000000000^1581 ≤ 1281889494691^1581*1000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423337307 1000000000 1281889494691 4000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4424486649/10000000000 : ℝ)^2093 ≤ (33976381145133/100000000000000 : ℝ)^1581 := by
    have hnat : (4424486649 : ℕ)^2093*100000000000000^1581 ≤ 33976381145133^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4424486649 10000000000 33976381145133 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212243341/5000000000 : ℝ)^2093 ≤ (8494095370153/25000000000000 : ℝ)^1581 := by
    have hnat : (2212243341 : ℕ)^2093*25000000000000^1581 ≤ 8494095370153^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212243341 5000000000 8494095370153 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423337307/1000000000 : ℝ), (4424486649/10000000000 : ℝ), (2212243341/5000000000 : ℝ)] ![(1281889494691/4000000000000 : ℝ), (33976381145133/100000000000000 : ℝ), (8494095370153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423337307/1000000000 : ℝ)|^2093 ≤ (1281889494691/4000000000000 : ℝ)^1581
        have hw : |(423337307/1000000000 : ℝ)|=(423337307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4424486649/10000000000 : ℝ)|^2093 ≤ (33976381145133/100000000000000 : ℝ)^1581
        have hw : |(4424486649/10000000000 : ℝ)|=(4424486649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2212243341/5000000000 : ℝ)|^2093 ≤ (8494095370153/25000000000000 : ℝ)^1581
        have hw : |(2212243341/5000000000 : ℝ)|=(2212243341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1179_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15559/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59327/100000 : ℝ) ∧ (79921/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83207/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5701/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5701/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5701/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5701/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5701/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5701/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5701/50000 : ℝ) ^ (8371/2048 : ℝ) ≤ (2795967215609453/20000000000000000000 : ℝ) := by
    have hpowers : (5701/50000 : ℝ)^8371 ≤ (2795967215609453/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5701 : ℕ)^8371*20000000000000000000^2048 ≤ 2795967215609453^2048*50000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5701 50000 2795967215609453 20000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5701/50000 : ℝ)) (X := (2795967215609453/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14069/100000 : ℝ) ^ (8371/2048 : ℝ) ≤ (16503616867015037/50000000000000000000 : ℝ) := by
    have hpowers : (14069/100000 : ℝ)^8371 ≤ (16503616867015037/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14069 : ℕ)^8371*50000000000000000000^2048 ≤ 16503616867015037^2048*100000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14069 100000 16503616867015037 50000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14069/100000 : ℝ)) (X := (16503616867015037/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002795967215609453/10000000000000000000 : ℝ) ≤ (10000683972798743/10000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (10002795967215609453/10000000000000000000 : ℝ)^2048 ≤ (10000683972798743/10000000000000000 : ℝ)^8371 := by
      have hnat : (10002795967215609453 : ℕ)^2048*10000000000000000^8371 ≤ 10000683972798743^8371*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002795967215609453 10000000000000000000 10000683972798743 10000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000683972798743/10000000000000000 : ℝ)) (X := (10002795967215609453/10000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046987069812077339/100000000000000000000 : ℝ) ≤ (10001149354282937/10000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (100046987069812077339/100000000000000000000 : ℝ)^2048 ≤ (10001149354282937/10000000000000000 : ℝ)^8371 := by
      have hnat : (100046987069812077339 : ℕ)^2048*10000000000000000^8371 ≤ 10001149354282937^8371*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046987069812077339 100000000000000000000 10001149354282937 10000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001149354282937/10000000000000000 : ℝ)) (X := (100046987069812077339/100000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016503616867015037/25000000000000000000 : ℝ) ≤ (10001614735767131/10000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (25016503616867015037/25000000000000000000 : ℝ)^2048 ≤ (10001614735767131/10000000000000000 : ℝ)^8371 := by
      have hnat : (25016503616867015037 : ℕ)^2048*10000000000000000^8371 ≤ 10001614735767131^8371*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016503616867015037 25000000000000000000 10001614735767131 10000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001614735767131/10000000000000000 : ℝ)) (X := (25016503616867015037/25000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2795967215609453/20000000000000000000 : ℝ) ≤ ((1777414106405912507/1778000000000000000 : ℝ)+2*(77563580699/44450000000000 : ℝ)*(5701/50000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (1777414106405912507/1778000000000000000 : ℝ)+2*(77563580699/44450000000000 : ℝ)*(5701/50000 : ℝ)=(10000683972798743/10000000000000000 : ℝ) by norm_num, show 1+2*(2795967215609453/20000000000000000000 : ℝ)=(10002795967215609453/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16503616867015037/50000000000000000000 : ℝ)+(2795967215609453/20000000000000000000 : ℝ) ≤ ((1777414106405912507/1778000000000000000 : ℝ)+(77563580699/44450000000000 : ℝ)*((14069/100000 : ℝ)+(5701/50000 : ℝ)))^(8371/2048 : ℝ) := by
    rw [show (1777414106405912507/1778000000000000000 : ℝ)+(77563580699/44450000000000 : ℝ)*((14069/100000 : ℝ)+(5701/50000 : ℝ))=(10001149354282937/10000000000000000 : ℝ) by norm_num, show 1+(16503616867015037/50000000000000000000 : ℝ)+(2795967215609453/20000000000000000000 : ℝ)=(100046987069812077339/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16503616867015037/50000000000000000000 : ℝ) ≤ ((1777414106405912507/1778000000000000000 : ℝ)+2*(77563580699/44450000000000 : ℝ)*(14069/100000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (1777414106405912507/1778000000000000000 : ℝ)+2*(77563580699/44450000000000 : ℝ)*(14069/100000 : ℝ)=(10001614735767131/10000000000000000 : ℝ) by norm_num, show 1+2*(16503616867015037/50000000000000000000 : ℝ)=(25016503616867015037/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1777414106405912507/1778000000000000000 : ℝ)*(X 1 0+X 2 0)+(77563580699/44450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (5701/50000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (1777414106405912507/1778000000000000000 : ℝ)) (alpha := (77563580699/44450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1777414106405912507/1778000000000000000 : ℝ)*(X 0 1+X 2 1)+(77563580699/44450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (5701/50000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (1777414106405912507/1778000000000000000 : ℝ)) (alpha := (77563580699/44450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1777414106405912507/1778000000000000000 : ℝ)*(X 0 2+X 1 2)+(77563580699/44450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (5701/50000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (1777414106405912507/1778000000000000000 : ℝ)) (alpha := (77563580699/44450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-505910659/2500000000 : ℝ)*X 0 0+(1075154553/2000000000 : ℝ)*X 0 1+(2687886429/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296314641/10000000000 : ℝ)*X 1 0+(-532872993/2500000000 : ℝ)*X 1 1+(5375772609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648157683/5000000000 : ℝ)*X 2 0+(1075154417/2000000000 : ℝ)*X 2 1+(-266436463/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1116659227/2500000000 : ℝ)*X 0 0+(861599581/2000000000 : ℝ)*X 0 1+(861599493/2000000000 : ℝ)*X 0 2+(1116659227/2500000000 : ℝ)*X 1 0+(861599581/2000000000 : ℝ)*X 1 1+(861599493/2000000000 : ℝ)*X 1 2+(1116659227/2500000000 : ℝ)*X 2 0+(861599581/2000000000 : ℝ)*X 2 1+(861599493/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2276379879/10000000000 : ℝ)*X 0 0+(5281598559/10000000000 : ℝ)*X 0 1+(2640799231/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681396839/5000000000 : ℝ)*X 1 0+(-542161267/2500000000 : ℝ)*X 1 1+(82524977/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362793861/10000000000 : ℝ)*X 2 0+(1320399629/2500000000 : ℝ)*X 2 1+(-2168644839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4251964353/10000000000 : ℝ)*X 0 0+(2207656669/5000000000 : ℝ)*X 0 1+(2207656741/5000000000 : ℝ)*X 0 2+(4251964353/10000000000 : ℝ)*X 1 0+(2207656669/5000000000 : ℝ)*X 1 1+(2207656741/5000000000 : ℝ)*X 1 2+(4251964353/10000000000 : ℝ)*X 2 0+(2207656669/5000000000 : ℝ)*X 2 1+(2207656741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-17787897/80000000 : ℝ)*X 0 0+(208699209/400000000 : ℝ)*X 0 1+(538538323/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289527893/10000000000 : ℝ)*X 1 0+(-66488483/312500000 : ℝ)*X 1 1+(5385382817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((165297743/312500000 : ℝ)*X 2 0+(2692691201/5000000000 : ℝ)*X 2 1+(-1063816087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4488271227/10000000000 : ℝ)*X 0 0+(537130003/1250000000 : ℝ)*X 0 1+(4297039997/10000000000 : ℝ)*X 0 2+(4488271227/10000000000 : ℝ)*X 1 0+(537130003/1250000000 : ℝ)*X 1 1+(4297039997/10000000000 : ℝ)*X 1 2+(4488271227/10000000000 : ℝ)*X 2 0+(537130003/1250000000 : ℝ)*X 2 1+(4297039997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2076832639/10000000000 : ℝ)*X 0 0+(679829941/1250000000 : ℝ)*X 0 1+(5273543973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368476983/10000000000 : ℝ)*X 1 0+(-542941599/2500000000 : ℝ)*X 1 1+(1318385981/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368476957/10000000000 : ℝ)*X 2 0+(2636772369/5000000000 : ℝ)*X 2 1+(-1085882673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((423337307/1000000000 : ℝ)*X 0 0+(4424486649/10000000000 : ℝ)*X 0 1+(2212243341/5000000000 : ℝ)*X 0 2+(423337307/1000000000 : ℝ)*X 1 0+(4424486649/10000000000 : ℝ)*X 1 1+(2212243341/5000000000 : ℝ)*X 1 2+(423337307/1000000000 : ℝ)*X 2 0+(4424486649/10000000000 : ℝ)*X 2 1+(2212243341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15559/25000 : ℝ) ≤ (-27662718552916446305121579539103/44450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46915117/50000000000000 : ℝ)*(upper0) + (9562449/50000000000000 : ℝ)*(lower1) + (79557749/50000000000000 : ℝ)*(lower2) + (2391223/20000000000000 : ℝ)*(lower3) + (1975789167488257/50000000000000 : ℝ)*(major0) + (1975789167488257/50000000000000 : ℝ)*(major1) + (1975789167488257/50000000000000 : ℝ)*(major2) + (181998487/25000000000000 : ℝ)*(sp3) + (5292953002955919/100000000000000 : ℝ)*(sp4) + (5292955678177403/100000000000000 : ℝ)*(sp5) + (2646423067527081/50000000000000 : ℝ)*(sp6) + (657736177410157/25000000000000 : ℝ)*(sp7) + (668805371/25000000000000 : ℝ)*(sp8) + (109543123241/100000000000000 : ℝ)*(sp14) + (164434089852161/6250000000000 : ℝ)*(f.failure) + (5292955678177403/100000000000000 : ℝ)*(f.sum) + (20839212790743/4445000000000000000000000000 : ℝ)*base66 + (23986138869264243/12700000000000000000000000000000 : ℝ)*base68 + (19487145949564243/12700000000000000000000000000000 : ℝ)*base70 + (45822199807164243/12700000000000000000000000000000 : ℝ)*base72 + (6251898632643/1111250000000000000000000000 : ℝ)*base73 + (66402887601764243/12700000000000000000000000000000 : ℝ)*base76 + (22441584353335757/12700000000000000000000000000000 : ℝ)*base77 + (46323539802435757/12700000000000000000000000000000 : ℝ)*base79 + (5374077171971/555625000000000000000000000 : ℝ)*base82 + (622787/312500000000000000000 : ℝ)*base89 + (622787/312500000000000000000 : ℝ)*base91 + (622787/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59327/100000 : ℝ) ≤ (52744255137466825680662506341027/88900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23206269/25000000000000 : ℝ)*(upper0) + (28612753/50000000000000 : ℝ)*(upper3) + (369115519/100000000000000 : ℝ)*(upper4) + (4016327672252787/100000000000000 : ℝ)*(major0) + (4016327672252787/100000000000000 : ℝ)*(major1) + (4016327672252787/100000000000000 : ℝ)*(major2) + (5338820171640563/100000000000000 : ℝ)*(sp0) + (1334655574089213/25000000000000 : ℝ)*(sp1) + (667324484649297/12500000000000 : ℝ)*(sp2) + (1337017878429099/50000000000000 : ℝ)*(sp3) + (651100889/20000000000000 : ℝ)*(sp8) + (40226157631/20000000000000 : ℝ)*(sp9) + (227549950631/100000000000000 : ℝ)*(sp10) + (19536903749/100000000000000 : ℝ)*(sp11) + (1337027646880973/50000000000000 : ℝ)*(f.failure) + (333676464196563/6250000000000 : ℝ)*(f.sum) + (174488747047/138906250000000000000000000 : ℝ)*base66 + (156044606239624713/25400000000000000000000000000000 : ℝ)*base68 + (35781225761024713/25400000000000000000000000000000 : ℝ)*base70 + (53515874613175287/25400000000000000000000000000000 : ℝ)*base71 + (51287303652241/1111250000000000000000000000 : ℝ)*base74 + (83393604475624713/25400000000000000000000000000000 : ℝ)*base76 + (65554694198175287/25400000000000000000000000000000 : ℝ)*base77 + (1442407865410424713/25400000000000000000000000000000 : ℝ)*base80 + (3078015061601/4445000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (23620809/2500000000000000000000 : ℝ)*base90 + (23620809/2500000000000000000000 : ℝ)*base92 + (23620809/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79921/100000 : ℝ) ≤ (7105182549672522794403625725831/8890000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (431782559/100000000000000 : ℝ)*(upper0) + (15350127/6250000000000 : ℝ)*(upper1) + (5293571/3125000000000 : ℝ)*(upper2) + (70643611/12500000000000 : ℝ)*(lower5) + (896779847938889/20000000000000 : ℝ)*(major0) + (896779847938889/20000000000000 : ℝ)*(major1) + (896779847938889/20000000000000 : ℝ)*(major2) + (146920843277/100000000000000 : ℝ)*(sp1) + (20483327021/100000000000000 : ℝ)*(sp3) + (6820185707/50000000000000 : ℝ)*(sp4) + (1488945278886029/25000000000000 : ℝ)*(sp8) + (2977823917536127/50000000000000 : ℝ)*(sp9) + (5955794755915531/100000000000000 : ℝ)*(sp10) + (298534213572311/10000000000000 : ℝ)*(sp11) + (746340654762533/25000000000000 : ℝ)*(f.failure) + (5955794755915531/100000000000000 : ℝ)*(f.sum) + (224492842013/444500000000000000000000000 : ℝ)*base66 + (29580437623933611/5080000000000000000000000000000 : ℝ)*base68 + (76000107059106389/5080000000000000000000000000000 : ℝ)*base69 + (766962966386389/5080000000000000000000000000000 : ℝ)*base71 + (9195314345131/889000000000000000000000000 : ℝ)*base74 + (23164453203066389/5080000000000000000000000000000 : ℝ)*base75 + (29776863407226389/5080000000000000000000000000000 : ℝ)*base77 + (40048140741186389/5080000000000000000000000000000 : ℝ)*base79 + (1308627711627/889000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (9823711/1250000000000000000000 : ℝ)*base89 + (9823711/1250000000000000000000 : ℝ)*base91 + (9823711/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83207/100000 : ℝ) ≤ (-18492172050532241369888557961583/22225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151342661/50000000000000 : ℝ)*(lower0) + (5258151/2500000000000 : ℝ)*(lower2) + (14894889/20000000000000 : ℝ)*(upper3) + (898919377/100000000000000 : ℝ)*(upper5) + (1129761126984459/25000000000000 : ℝ)*(major0) + (1129761126984459/25000000000000 : ℝ)*(major1) + (1129761126984459/25000000000000 : ℝ)*(major2) + (5288317241/25000000000000 : ℝ)*(sp0) + (12430839101/3125000000000 : ℝ)*(sp5) + (272954427/195312500000 : ℝ)*(sp7) + (6057040452312589/100000000000000 : ℝ)*(sp12) + (3028331909365161/50000000000000 : ℝ)*(sp13) + (6057061605581553/100000000000000 : ℝ)*(sp14) + (3008622448854379/100000000000000 : ℝ)*(sp15) + (752190550380251/25000000000000 : ℝ)*(f.failure) + (6057061605581553/100000000000000 : ℝ)*(f.sum) + (12990704868787/4445000000000000000000000000 : ℝ)*base66 + (86178097073483041/6350000000000000000000000000000 : ℝ)*base68 + (15673793835483041/6350000000000000000000000000000 : ℝ)*base70 + (51961231858633041/6350000000000000000000000000000 : ℝ)*base72 + (54334833024953/4445000000000000000000000000 : ℝ)*base73 + (11774225910733041/6350000000000000000000000000000 : ℝ)*base76 + (10225757792283041/6350000000000000000000000000000 : ℝ)*base78 + (132626027177183041/6350000000000000000000000000000 : ℝ)*base80 + (4692252967833/1111250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (15074817/1250000000000000000000 : ℝ)*base89 + (15074817/1250000000000000000000 : ℝ)*base91 + (15074817/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1179_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59327/100000 : ℝ) else (79921/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83207/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1179_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1179_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59327/100000 : ℝ) else (79921/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83207/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1179_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1179_s10 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1179_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59327/100000 : ℝ) else (79921/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83207/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1179_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
