-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1658_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:15.584058+00:00
-- url     : https://prove2.me/submissions/f40ef577-ab3e-4ecd-a0ec-17ee5418a823

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
theorem support_rectangle_w1658_s0_0 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-59148851/400000000 : ℝ)*x 0 + (5775473221/10000000000 : ℝ)*x 1 + (2463470663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59148851/400000000 : ℝ)^4951 ≤ (4386285353/48828125000 : ℝ)^3927 := by
    have hnat : (59148851 : ℕ)^4951*48828125000^3927 ≤ 4386285353^3927*400000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59148851 400000000 4386285353 48828125000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5775473221/10000000000 : ℝ)^4951 ≤ (25025884115249/50000000000000 : ℝ)^3927 := by
    have hnat : (5775473221 : ℕ)^4951*50000000000000^3927 ≤ 25025884115249^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5775473221 10000000000 25025884115249 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2463470663/5000000000 : ℝ)^4951 ≤ (10241279838473/25000000000000 : ℝ)^3927 := by
    have hnat : (2463470663 : ℕ)^4951*25000000000000^3927 ≤ 10241279838473^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463470663 5000000000 10241279838473 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59148851/400000000 : ℝ), (5775473221/10000000000 : ℝ), (2463470663/5000000000 : ℝ)] ![(4386285353/48828125000 : ℝ), (25025884115249/50000000000000 : ℝ), (10241279838473/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59148851/400000000 : ℝ)|^4951 ≤ (4386285353/48828125000 : ℝ)^3927
        have hw : |(-59148851/400000000 : ℝ)|=(59148851/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5775473221/10000000000 : ℝ)|^4951 ≤ (25025884115249/50000000000000 : ℝ)^3927
        have hw : |(5775473221/10000000000 : ℝ)|=(5775473221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2463470663/5000000000 : ℝ)|^4951 ≤ (10241279838473/25000000000000 : ℝ)^3927
        have hw : |(2463470663/5000000000 : ℝ)|=(2463470663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s0_1 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2717188829/5000000000 : ℝ)*x 0 + (-1943750059/10000000000 : ℝ)*x 1 + (1231735481/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2717188829/5000000000 : ℝ)^4951 ≤ (46354060898207/100000000000000 : ℝ)^3927 := by
    have hnat : (2717188829 : ℕ)^4951*100000000000000^3927 ≤ 46354060898207^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717188829 5000000000 46354060898207 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1943750059/10000000000 : ℝ)^4951 ≤ (3170203366391/25000000000000 : ℝ)^3927 := by
    have hnat : (1943750059 : ℕ)^4951*25000000000000^3927 ≤ 3170203366391^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943750059 10000000000 3170203366391 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1231735481/2500000000 : ℝ)^4951 ≤ (8193025124497/20000000000000 : ℝ)^3927 := by
    have hnat : (1231735481 : ℕ)^4951*20000000000000^3927 ≤ 8193025124497^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231735481 2500000000 8193025124497 20000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2717188829/5000000000 : ℝ), (-1943750059/10000000000 : ℝ), (1231735481/2500000000 : ℝ)] ![(46354060898207/100000000000000 : ℝ), (3170203366391/25000000000000 : ℝ), (8193025124497/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2717188829/5000000000 : ℝ)|^4951 ≤ (46354060898207/100000000000000 : ℝ)^3927
        have hw : |(2717188829/5000000000 : ℝ)|=(2717188829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1943750059/10000000000 : ℝ)|^4951 ≤ (3170203366391/25000000000000 : ℝ)^3927
        have hw : |(-1943750059/10000000000 : ℝ)|=(1943750059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1231735481/2500000000 : ℝ)|^4951 ≤ (8193025124497/20000000000000 : ℝ)^3927
        have hw : |(1231735481/2500000000 : ℝ)|=(1231735481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s0_2 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5434378863/10000000000 : ℝ)*x 0 + (2463470533/5000000000 : ℝ)*x 1 + (-1943749577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5434378863/10000000000 : ℝ)^4951 ≤ (5794259232097/12500000000000 : ℝ)^3927 := by
    have hnat : (5434378863 : ℕ)^4951*12500000000000^3927 ≤ 5794259232097^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434378863 10000000000 5794259232097 12500000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2463470533/5000000000 : ℝ)^4951 ≤ (40965116628417/100000000000000 : ℝ)^3927 := by
    have hnat : (2463470533 : ℕ)^4951*100000000000000^3927 ≤ 40965116628417^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463470533 5000000000 40965116628417 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1943749577/10000000000 : ℝ)^4951 ≤ (12680809501089/100000000000000 : ℝ)^3927 := by
    have hnat : (1943749577 : ℕ)^4951*100000000000000^3927 ≤ 12680809501089^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943749577 10000000000 12680809501089 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5434378863/10000000000 : ℝ), (2463470533/5000000000 : ℝ), (-1943749577/10000000000 : ℝ)] ![(5794259232097/12500000000000 : ℝ), (40965116628417/100000000000000 : ℝ), (12680809501089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5434378863/10000000000 : ℝ)|^4951 ≤ (5794259232097/12500000000000 : ℝ)^3927
        have hw : |(5434378863/10000000000 : ℝ)|=(5434378863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2463470533/5000000000 : ℝ)|^4951 ≤ (40965116628417/100000000000000 : ℝ)^3927
        have hw : |(2463470533/5000000000 : ℝ)|=(2463470533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1943749577/10000000000 : ℝ)|^4951 ≤ (12680809501089/100000000000000 : ℝ)^3927
        have hw : |(-1943749577/10000000000 : ℝ)|=(1943749577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s0_3 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4086886809/10000000000 : ℝ)*x 0 + (1542330427/5000000000 : ℝ)*x 1 + (5302167697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4086886809/10000000000 : ℝ)^4951 ≤ (8090955311143/25000000000000 : ℝ)^3927 := by
    have hnat : (4086886809 : ℕ)^4951*25000000000000^3927 ≤ 8090955311143^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4086886809 10000000000 8090955311143 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1542330427/5000000000 : ℝ)^4951 ≤ (22699366521889/100000000000000 : ℝ)^3927 := by
    have hnat : (1542330427 : ℕ)^4951*100000000000000^3927 ≤ 22699366521889^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542330427 5000000000 22699366521889 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5302167697/10000000000 : ℝ)^4951 ≤ (44936812224837/100000000000000 : ℝ)^3927 := by
    have hnat : (5302167697 : ℕ)^4951*100000000000000^3927 ≤ 44936812224837^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302167697 10000000000 44936812224837 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4086886809/10000000000 : ℝ), (1542330427/5000000000 : ℝ), (5302167697/10000000000 : ℝ)] ![(8090955311143/25000000000000 : ℝ), (22699366521889/100000000000000 : ℝ), (44936812224837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4086886809/10000000000 : ℝ)|^4951 ≤ (8090955311143/25000000000000 : ℝ)^3927
        have hw : |(4086886809/10000000000 : ℝ)|=(4086886809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1542330427/5000000000 : ℝ)|^4951 ≤ (22699366521889/100000000000000 : ℝ)^3927
        have hw : |(1542330427/5000000000 : ℝ)|=(1542330427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5302167697/10000000000 : ℝ)|^4951 ≤ (44936812224837/100000000000000 : ℝ)^3927
        have hw : |(5302167697/10000000000 : ℝ)|=(5302167697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s0_4 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1480930353/10000000000 : ℝ)*x 0 + (4947898313/10000000000 : ℝ)*x 1 + (179806133/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1480930353/10000000000 : ℝ)^4951 ≤ (4500017521921/50000000000000 : ℝ)^3927 := by
    have hnat : (1480930353 : ℕ)^4951*50000000000000^3927 ≤ 4500017521921^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480930353 10000000000 4500017521921 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4947898313/10000000000 : ℝ)^4951 ≤ (4118492469113/10000000000000 : ℝ)^3927 := by
    have hnat : (4947898313 : ℕ)^4951*10000000000000^3927 ≤ 4118492469113^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4947898313 10000000000 4118492469113 10000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179806133/312500000 : ℝ)^4951 ≤ (24907520128427/50000000000000 : ℝ)^3927 := by
    have hnat : (179806133 : ℕ)^4951*50000000000000^3927 ≤ 24907520128427^3927*312500000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179806133 312500000 24907520128427 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1480930353/10000000000 : ℝ), (4947898313/10000000000 : ℝ), (179806133/312500000 : ℝ)] ![(4500017521921/50000000000000 : ℝ), (4118492469113/10000000000000 : ℝ), (24907520128427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1480930353/10000000000 : ℝ)|^4951 ≤ (4500017521921/50000000000000 : ℝ)^3927
        have hw : |(-1480930353/10000000000 : ℝ)|=(1480930353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4947898313/10000000000 : ℝ)|^4951 ≤ (4118492469113/10000000000000 : ℝ)^3927
        have hw : |(4947898313/10000000000 : ℝ)|=(4947898313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179806133/312500000 : ℝ)|^4951 ≤ (24907520128427/50000000000000 : ℝ)^3927
        have hw : |(179806133/312500000 : ℝ)|=(179806133/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s0_5 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202895377/10000000000 : ℝ)*x 0 + (-1116896851/10000000000 : ℝ)*x 1 + (2876897881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202895377/10000000000 : ℝ)^4951 ≤ (43878673505339/100000000000000 : ℝ)^3927 := by
    have hnat : (5202895377 : ℕ)^4951*100000000000000^3927 ≤ 43878673505339^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202895377 10000000000 43878673505339 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1116896851/10000000000 : ℝ)^4951 ≤ (394143225897/6250000000000 : ℝ)^3927 := by
    have hnat : (1116896851 : ℕ)^4951*6250000000000^3927 ≤ 394143225897^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116896851 10000000000 394143225897 6250000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2876897881/5000000000 : ℝ)^4951 ≤ (24907517432333/50000000000000 : ℝ)^3927 := by
    have hnat : (2876897881 : ℕ)^4951*50000000000000^3927 ≤ 24907517432333^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876897881 5000000000 24907517432333 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202895377/10000000000 : ℝ), (-1116896851/10000000000 : ℝ), (2876897881/5000000000 : ℝ)] ![(43878673505339/100000000000000 : ℝ), (394143225897/6250000000000 : ℝ), (24907517432333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202895377/10000000000 : ℝ)|^4951 ≤ (43878673505339/100000000000000 : ℝ)^3927
        have hw : |(5202895377/10000000000 : ℝ)|=(5202895377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1116896851/10000000000 : ℝ)|^4951 ≤ (394143225897/6250000000000 : ℝ)^3927
        have hw : |(-1116896851/10000000000 : ℝ)|=(1116896851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2876897881/5000000000 : ℝ)|^4951 ≤ (24907517432333/50000000000000 : ℝ)^3927
        have hw : |(2876897881/5000000000 : ℝ)|=(2876897881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s0_6 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (325180891/625000000 : ℝ)*x 0 + (5753797563/10000000000 : ℝ)*x 1 + (-279223941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (325180891/625000000 : ℝ)^4951 ≤ (43878661586169/100000000000000 : ℝ)^3927 := by
    have hnat : (325180891 : ℕ)^4951*100000000000000^3927 ≤ 43878661586169^3927*625000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325180891 625000000 43878661586169 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5753797563/10000000000 : ℝ)^4951 ≤ (12453763630807/25000000000000 : ℝ)^3927 := by
    have hnat : (5753797563 : ℕ)^4951*25000000000000^3927 ≤ 12453763630807^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5753797563 10000000000 12453763630807 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279223941/2500000000 : ℝ)^4951 ≤ (6306283876463/100000000000000 : ℝ)^3927 := by
    have hnat : (279223941 : ℕ)^4951*100000000000000^3927 ≤ 6306283876463^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279223941 2500000000 6306283876463 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(325180891/625000000 : ℝ), (5753797563/10000000000 : ℝ), (-279223941/2500000000 : ℝ)] ![(43878661586169/100000000000000 : ℝ), (12453763630807/25000000000000 : ℝ), (6306283876463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(325180891/625000000 : ℝ)|^4951 ≤ (43878661586169/100000000000000 : ℝ)^3927
        have hw : |(325180891/625000000 : ℝ)|=(325180891/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5753797563/10000000000 : ℝ)|^4951 ≤ (12453763630807/25000000000000 : ℝ)^3927
        have hw : |(5753797563/10000000000 : ℝ)|=(5753797563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279223941/2500000000 : ℝ)|^4951 ≤ (6306283876463/100000000000000 : ℝ)^3927
        have hw : |(-279223941/2500000000 : ℝ)|=(279223941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s0_7 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4092650941/10000000000 : ℝ)*x 0 + (5247401633/10000000000 : ℝ)*x 1 + (1570655573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4092650941/10000000000 : ℝ)^4951 ≤ (16210690103249/50000000000000 : ℝ)^3927 := by
    have hnat : (4092650941 : ℕ)^4951*50000000000000^3927 ≤ 16210690103249^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4092650941 10000000000 16210690103249 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247401633/10000000000 : ℝ)^4951 ≤ (44352418417669/100000000000000 : ℝ)^3927 := by
    have hnat : (5247401633 : ℕ)^4951*100000000000000^3927 ≤ 44352418417669^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247401633 10000000000 44352418417669 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1570655573/5000000000 : ℝ)^4951 ≤ (11613100678941/50000000000000 : ℝ)^3927 := by
    have hnat : (1570655573 : ℕ)^4951*50000000000000^3927 ≤ 11613100678941^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570655573 5000000000 11613100678941 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4092650941/10000000000 : ℝ), (5247401633/10000000000 : ℝ), (1570655573/5000000000 : ℝ)] ![(16210690103249/50000000000000 : ℝ), (44352418417669/100000000000000 : ℝ), (11613100678941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4092650941/10000000000 : ℝ)|^4951 ≤ (16210690103249/50000000000000 : ℝ)^3927
        have hw : |(4092650941/10000000000 : ℝ)|=(4092650941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247401633/10000000000 : ℝ)|^4951 ≤ (44352418417669/100000000000000 : ℝ)^3927
        have hw : |(5247401633/10000000000 : ℝ)|=(5247401633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1570655573/5000000000 : ℝ)|^4951 ≤ (11613100678941/50000000000000 : ℝ)^3927
        have hw : |(1570655573/5000000000 : ℝ)|=(1570655573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1658_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4997/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5797/25000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4947/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4947 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4947*1^1024 ≤ 0^1024*1^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4947/1024 : ℝ) ≤ (597723127400946251/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4947 ≤ (597723127400946251/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4947*50000000000000000000^1024 ≤ 597723127400946251^1024*5^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 597723127400946251 50000000000000000000 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (597723127400946251/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4947 := by
      have hnat : (1 : ℕ)^1024*1^4947 ≤ 1^4947*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50597723127400946251/50000000000000000000 : ℝ) ≤ (1002462857681111/1000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (50597723127400946251/50000000000000000000 : ℝ)^1024 ≤ (1002462857681111/1000000000000000 : ℝ)^4947 := by
      have hnat : (50597723127400946251 : ℕ)^1024*1000000000000000^4947 ≤ 1002462857681111^4947*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50597723127400946251 50000000000000000000 1002462857681111 1000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002462857681111/1000000000000000 : ℝ)) (X := (50597723127400946251/50000000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25597723127400946251/25000000000000000000 : ℝ) ≤ (502462857681111/500000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (25597723127400946251/25000000000000000000 : ℝ)^1024 ≤ (502462857681111/500000000000000 : ℝ)^4947 := by
      have hnat : (25597723127400946251 : ℕ)^1024*500000000000000^4947 ≤ 502462857681111^4947*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25597723127400946251 25000000000000000000 502462857681111 500000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502462857681111/500000000000000 : ℝ)) (X := (25597723127400946251/25000000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2462857681111/400000000000000 : ℝ)*(0 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2462857681111/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(597723127400946251/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2462857681111/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4947/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2462857681111/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1002462857681111/1000000000000000 : ℝ) by norm_num, show 1+(597723127400946251/50000000000000000000 : ℝ)+(0 : ℝ)=(50597723127400946251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(597723127400946251/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2462857681111/400000000000000 : ℝ)*(2/5 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2462857681111/400000000000000 : ℝ)*(2/5 : ℝ)=(502462857681111/500000000000000 : ℝ) by norm_num, show 1+2*(597723127400946251/50000000000000000000 : ℝ)=(25597723127400946251/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2462857681111/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2462857681111/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2462857681111/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2462857681111/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2462857681111/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2462857681111/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-59148851/400000000 : ℝ)*X 0 0+(5775473221/10000000000 : ℝ)*X 0 1+(2463470663/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2717188829/5000000000 : ℝ)*X 1 0+(-1943750059/10000000000 : ℝ)*X 1 1+(1231735481/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5434378863/10000000000 : ℝ)*X 2 0+(2463470533/5000000000 : ℝ)*X 2 1+(-1943749577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4086886809/10000000000 : ℝ)*X 0 0+(1542330427/5000000000 : ℝ)*X 0 1+(5302167697/10000000000 : ℝ)*X 0 2+(4086886809/10000000000 : ℝ)*X 1 0+(1542330427/5000000000 : ℝ)*X 1 1+(5302167697/10000000000 : ℝ)*X 1 2+(4086886809/10000000000 : ℝ)*X 2 0+(1542330427/5000000000 : ℝ)*X 2 1+(5302167697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1480930353/10000000000 : ℝ)*X 0 0+(4947898313/10000000000 : ℝ)*X 0 1+(179806133/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5202895377/10000000000 : ℝ)*X 1 0+(-1116896851/10000000000 : ℝ)*X 1 1+(2876897881/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((325180891/625000000 : ℝ)*X 2 0+(5753797563/10000000000 : ℝ)*X 2 1+(-279223941/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4092650941/10000000000 : ℝ)*X 0 0+(5247401633/10000000000 : ℝ)*X 0 1+(1570655573/5000000000 : ℝ)*X 0 2+(4092650941/10000000000 : ℝ)*X 1 0+(5247401633/10000000000 : ℝ)*X 1 1+(1570655573/5000000000 : ℝ)*X 1 2+(4092650941/10000000000 : ℝ)*X 2 0+(5247401633/10000000000 : ℝ)*X 2 1+(1570655573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6350936032557959149239/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7104089/5000000000000 : ℝ)*(base1) + (145261613/12500000000000 : ℝ)*(base19) + (1423412801/100000000000000 : ℝ)*(base23) + (3010317/10000000000000 : ℝ)*(upper3) + (65463701/25000000000000 : ℝ)*(upper5) + (203684792315283/25000000000000 : ℝ)*(major0) + (203684792315283/25000000000000 : ℝ)*(major1) + (203684792315283/25000000000000 : ℝ)*(major2) + (1178510153888263/100000000000000 : ℝ)*(sp0) + (1178515621224909/100000000000000 : ℝ)*(sp1) + (294628839976253/25000000000000 : ℝ)*(sp2) + (112739819937061/25000000000000 : ℝ)*(sp3) + (677151133/10000000000000 : ℝ)*(sp4) + (480419139/25000000000000 : ℝ)*(sp7) + (22548067175329/5000000000000 : ℝ)*(f.failure) + (1178516783317813/100000000000000 : ℝ)*(f.sum) + (14999103165587/5000000000000000000000000000 : ℝ)*base66 + (921291650587/10000000000000000000000000000 : ℝ)*base68 + (47766141099413/10000000000000000000000000000 : ℝ)*base69 + (11660171420587/10000000000000000000000000000 : ℝ)*base72 + (20343997745587/5000000000000000000000000000 : ℝ)*base74 + (30319335880587/10000000000000000000000000000 : ℝ)*base76 + (38953760587/10000000000000000000000000000 : ℝ)*base78 + (54240605440587/10000000000000000000000000000 : ℝ)*base80 + (7296750880587/5000000000000000000000000000 : ℝ)*base82 + (472903/250000000000000000000 : ℝ)*base90 + (472903/250000000000000000000 : ℝ)*base92 + (472903/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10391896932456418889889/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42632071/20000000000000 : ℝ)*(base19) + (948361267/100000000000000 : ℝ)*(base23) + (367045063/100000000000000 : ℝ)*(base39) + (36486647/12500000000000 : ℝ)*(upper2) + (3651797/12500000000000 : ℝ)*(upper3) + (268861897/100000000000000 : ℝ)*(upper5) + (214457549861699/25000000000000 : ℝ)*(major0) + (214457549861699/25000000000000 : ℝ)*(major1) + (857829832401733/100000000000000 : ℝ)*(major2) + (442938143/25000000000000 : ℝ)*(sp2) + (1240847459985441/100000000000000 : ℝ)*(sp4) + (620423623412543/50000000000000 : ℝ)*(sp5) + (620422553458333/50000000000000 : ℝ)*(sp6) + (593515498331/125000000000 : ℝ)*(sp7) + (593515498331/125000000000 : ℝ)*(f.failure) + (248169565406101/20000000000000 : ℝ)*(f.sum) + (158596291355719/40000000000000000000000000000 : ℝ)*base65 + (7184980445363/40000000000000000000000000000 : ℝ)*base67 + (9323802292411/10000000000000000000000000000 : ℝ)*base70 + (20283988885363/40000000000000000000000000000 : ℝ)*base71 + (83003167875719/40000000000000000000000000000 : ℝ)*base73 + (15258431347589/10000000000000000000000000000 : ℝ)*base75 + (29425434652411/10000000000000000000000000000 : ℝ)*base78 + (5266356432411/10000000000000000000000000000 : ℝ)*base80 + (9481084992411/5000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (16717/6250000000000000000 : ℝ)*base90 + (16717/6250000000000000000 : ℝ)*base92 + (16717/6250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1658_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4997/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5797/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1658_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1658_s1_0 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1581338043/10000000000 : ℝ)*x 0 + (5490395153/10000000000 : ℝ)*x 1 + (1029050597/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1581338043/10000000000 : ℝ)^4951 ≤ (4888024016811/50000000000000 : ℝ)^3927 := by
    have hnat : (1581338043 : ℕ)^4951*50000000000000^3927 ≤ 4888024016811^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581338043 10000000000 4888024016811 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490395153/10000000000 : ℝ)^4951 ≤ (46957280553353/100000000000000 : ℝ)^3927 := by
    have hnat : (5490395153 : ℕ)^4951*100000000000000^3927 ≤ 46957280553353^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490395153 10000000000 46957280553353 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029050597/2000000000 : ℝ)^4951 ≤ (2163333569863/5000000000000 : ℝ)^3927 := by
    have hnat : (1029050597 : ℕ)^4951*5000000000000^3927 ≤ 2163333569863^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029050597 2000000000 2163333569863 5000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1581338043/10000000000 : ℝ), (5490395153/10000000000 : ℝ), (1029050597/2000000000 : ℝ)] ![(4888024016811/50000000000000 : ℝ), (46957280553353/100000000000000 : ℝ), (2163333569863/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1581338043/10000000000 : ℝ)|^4951 ≤ (4888024016811/50000000000000 : ℝ)^3927
        have hw : |(-1581338043/10000000000 : ℝ)|=(1581338043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490395153/10000000000 : ℝ)|^4951 ≤ (46957280553353/100000000000000 : ℝ)^3927
        have hw : |(5490395153/10000000000 : ℝ)|=(5490395153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1029050597/2000000000 : ℝ)|^4951 ≤ (2163333569863/5000000000000 : ℝ)^3927
        have hw : |(1029050597/2000000000 : ℝ)|=(1029050597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s1_1 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358548191/10000000000 : ℝ)*x 0 + (-1760587763/10000000000 : ℝ)*x 1 + (1029050559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358548191/10000000000 : ℝ)^4951 ≤ (5692509946339/12500000000000 : ℝ)^3927 := by
    have hnat : (5358548191 : ℕ)^4951*12500000000000^3927 ≤ 5692509946339^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358548191 10000000000 5692509946339 12500000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1760587763/10000000000 : ℝ)^4951 ≤ (11193251025473/100000000000000 : ℝ)^3927 := by
    have hnat : (1760587763 : ℕ)^4951*100000000000000^3927 ≤ 11193251025473^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760587763 10000000000 11193251025473 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029050559/2000000000 : ℝ)^4951 ≤ (21633334691461/50000000000000 : ℝ)^3927 := by
    have hnat : (1029050559 : ℕ)^4951*50000000000000^3927 ≤ 21633334691461^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029050559 2000000000 21633334691461 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358548191/10000000000 : ℝ), (-1760587763/10000000000 : ℝ), (1029050559/2000000000 : ℝ)] ![(5692509946339/12500000000000 : ℝ), (11193251025473/100000000000000 : ℝ), (21633334691461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358548191/10000000000 : ℝ)|^4951 ≤ (5692509946339/12500000000000 : ℝ)^3927
        have hw : |(5358548191/10000000000 : ℝ)|=(5358548191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1760587763/10000000000 : ℝ)|^4951 ≤ (11193251025473/100000000000000 : ℝ)^3927
        have hw : |(-1760587763/10000000000 : ℝ)|=(1760587763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1029050559/2000000000 : ℝ)|^4951 ≤ (21633334691461/50000000000000 : ℝ)^3927
        have hw : |(1029050559/2000000000 : ℝ)|=(1029050559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s1_2 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679273821/5000000000 : ℝ)*x 0 + (5145253377/10000000000 : ℝ)*x 1 + (-1760587727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679273821/5000000000 : ℝ)^4951 ≤ (1138501842209/2500000000000 : ℝ)^3927 := by
    have hnat : (2679273821 : ℕ)^4951*2500000000000^3927 ≤ 1138501842209^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679273821 5000000000 1138501842209 2500000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5145253377/10000000000 : ℝ)^4951 ≤ (21633337776579/50000000000000 : ℝ)^3927 := by
    have hnat : (5145253377 : ℕ)^4951*50000000000000^3927 ≤ 21633337776579^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145253377 10000000000 21633337776579 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1760587727/10000000000 : ℝ)^4951 ≤ (2238650147383/20000000000000 : ℝ)^3927 := by
    have hnat : (1760587727 : ℕ)^4951*20000000000000^3927 ≤ 2238650147383^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760587727 10000000000 2238650147383 20000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679273821/5000000000 : ℝ), (5145253377/10000000000 : ℝ), (-1760587727/10000000000 : ℝ)] ![(1138501842209/2500000000000 : ℝ), (21633337776579/50000000000000 : ℝ), (2238650147383/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679273821/5000000000 : ℝ)|^4951 ≤ (1138501842209/2500000000000 : ℝ)^3927
        have hw : |(2679273821/5000000000 : ℝ)|=(2679273821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5145253377/10000000000 : ℝ)|^4951 ≤ (21633337776579/50000000000000 : ℝ)^3927
        have hw : |(5145253377/10000000000 : ℝ)|=(5145253377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1760587727/10000000000 : ℝ)|^4951 ≤ (2238650147383/20000000000000 : ℝ)^3927
        have hw : |(-1760587727/10000000000 : ℝ)|=(1760587727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s1_3 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4167828431/10000000000 : ℝ)*x 0 + (3734295573/10000000000 : ℝ)*x 1 + (2318135457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4167828431/10000000000 : ℝ)^4951 ≤ (33174009019637/100000000000000 : ℝ)^3927 := by
    have hnat : (4167828431 : ℕ)^4951*100000000000000^3927 ≤ 33174009019637^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167828431 10000000000 33174009019637 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3734295573/10000000000 : ℝ)^4951 ≤ (28884065430953/100000000000000 : ℝ)^3927 := by
    have hnat : (3734295573 : ℕ)^4951*100000000000000^3927 ≤ 28884065430953^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734295573 10000000000 28884065430953 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2318135457/5000000000 : ℝ)^4951 ≤ (18970962768059/50000000000000 : ℝ)^3927 := by
    have hnat : (2318135457 : ℕ)^4951*50000000000000^3927 ≤ 18970962768059^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2318135457 5000000000 18970962768059 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4167828431/10000000000 : ℝ), (3734295573/10000000000 : ℝ), (2318135457/5000000000 : ℝ)] ![(33174009019637/100000000000000 : ℝ), (28884065430953/100000000000000 : ℝ), (18970962768059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4167828431/10000000000 : ℝ)|^4951 ≤ (33174009019637/100000000000000 : ℝ)^3927
        have hw : |(4167828431/10000000000 : ℝ)|=(4167828431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3734295573/10000000000 : ℝ)|^4951 ≤ (28884065430953/100000000000000 : ℝ)^3927
        have hw : |(3734295573/10000000000 : ℝ)|=(3734295573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2318135457/5000000000 : ℝ)|^4951 ≤ (18970962768059/50000000000000 : ℝ)^3927
        have hw : |(2318135457/5000000000 : ℝ)|=(2318135457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s1_4 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-395371003/2500000000 : ℝ)*x 0 + (5148712289/10000000000 : ℝ)*x 1 + (2743443909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (395371003/2500000000 : ℝ)^4951 ≤ (4888592878251/50000000000000 : ℝ)^3927 := by
    have hnat : (395371003 : ℕ)^4951*50000000000000^3927 ≤ 4888592878251^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395371003 2500000000 4888592878251 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5148712289/10000000000 : ℝ)^4951 ≤ (2706459336913/6250000000000 : ℝ)^3927 := by
    have hnat : (5148712289 : ℕ)^4951*6250000000000^3927 ≤ 2706459336913^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5148712289 10000000000 2706459336913 6250000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743443909/5000000000 : ℝ)^4951 ≤ (117298662071/250000000000 : ℝ)^3927 := by
    have hnat : (2743443909 : ℕ)^4951*250000000000^3927 ≤ 117298662071^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743443909 5000000000 117298662071 250000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-395371003/2500000000 : ℝ), (5148712289/10000000000 : ℝ), (2743443909/5000000000 : ℝ)] ![(4888592878251/50000000000000 : ℝ), (2706459336913/6250000000000 : ℝ), (117298662071/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-395371003/2500000000 : ℝ)|^4951 ≤ (4888592878251/50000000000000 : ℝ)^3927
        have hw : |(-395371003/2500000000 : ℝ)|=(395371003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5148712289/10000000000 : ℝ)|^4951 ≤ (2706459336913/6250000000000 : ℝ)^3927
        have hw : |(5148712289/10000000000 : ℝ)|=(5148712289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743443909/5000000000 : ℝ)|^4951 ≤ (117298662071/250000000000 : ℝ)^3927
        have hw : |(2743443909/5000000000 : ℝ)|=(2743443909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s1_5 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266192437/10000000000 : ℝ)*x 0 + (-354738233/2500000000 : ℝ)*x 1 + (5486887871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266192437/10000000000 : ℝ)^4951 ≤ (4455275161713/10000000000000 : ℝ)^3927 := by
    have hnat : (5266192437 : ℕ)^4951*10000000000000^3927 ≤ 4455275161713^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266192437 10000000000 4455275161713 10000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354738233/2500000000 : ℝ)^4951 ≤ (1065972870517/12500000000000 : ℝ)^3927 := by
    have hnat : (354738233 : ℕ)^4951*12500000000000^3927 ≤ 1065972870517^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354738233 2500000000 1065972870517 12500000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486887871/10000000000 : ℝ)^4951 ≤ (46919465399793/100000000000000 : ℝ)^3927 := by
    have hnat : (5486887871 : ℕ)^4951*100000000000000^3927 ≤ 46919465399793^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486887871 10000000000 46919465399793 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266192437/10000000000 : ℝ), (-354738233/2500000000 : ℝ), (5486887871/10000000000 : ℝ)] ![(4455275161713/10000000000000 : ℝ), (1065972870517/12500000000000 : ℝ), (46919465399793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266192437/10000000000 : ℝ)|^4951 ≤ (4455275161713/10000000000000 : ℝ)^3927
        have hw : |(5266192437/10000000000 : ℝ)|=(5266192437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-354738233/2500000000 : ℝ)|^4951 ≤ (1065972870517/12500000000000 : ℝ)^3927
        have hw : |(-354738233/2500000000 : ℝ)|=(354738233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486887871/10000000000 : ℝ)|^4951 ≤ (46919465399793/100000000000000 : ℝ)^3927
        have hw : |(5486887871/10000000000 : ℝ)|=(5486887871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s1_6 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633096109/5000000000 : ℝ)*x 0 + (5486888159/10000000000 : ℝ)*x 1 + (-11085569/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633096109/5000000000 : ℝ)^4951 ≤ (44552749281231/100000000000000 : ℝ)^3927 := by
    have hnat : (2633096109 : ℕ)^4951*100000000000000^3927 ≤ 44552749281231^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633096109 5000000000 44552749281231 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486888159/10000000000 : ℝ)^4951 ≤ (46919468504721/100000000000000 : ℝ)^3927 := by
    have hnat : (5486888159 : ℕ)^4951*100000000000000^3927 ≤ 46919468504721^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486888159 10000000000 46919468504721 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11085569/78125000 : ℝ)^4951 ≤ (8527782206431/100000000000000 : ℝ)^3927 := by
    have hnat : (11085569 : ℕ)^4951*100000000000000^3927 ≤ 8527782206431^3927*78125000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11085569 78125000 8527782206431 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633096109/5000000000 : ℝ), (5486888159/10000000000 : ℝ), (-11085569/78125000 : ℝ)] ![(44552749281231/100000000000000 : ℝ), (46919468504721/100000000000000 : ℝ), (8527782206431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633096109/5000000000 : ℝ)|^4951 ≤ (44552749281231/100000000000000 : ℝ)^3927
        have hw : |(2633096109/5000000000 : ℝ)|=(2633096109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486888159/10000000000 : ℝ)|^4951 ≤ (46919468504721/100000000000000 : ℝ)^3927
        have hw : |(5486888159/10000000000 : ℝ)|=(5486888159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11085569/78125000 : ℝ)|^4951 ≤ (8527782206431/100000000000000 : ℝ)^3927
        have hw : |(-11085569/78125000 : ℝ)|=(11085569/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s1_7 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (833642061/2000000000 : ℝ)*x 0 + (4627231039/10000000000 : ℝ)*x 1 + (3743461759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833642061/2000000000 : ℝ)^4951 ≤ (829446029887/2500000000000 : ℝ)^3927 := by
    have hnat : (833642061 : ℕ)^4951*2500000000000^3927 ≤ 829446029887^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833642061 2000000000 829446029887 2500000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4627231039/10000000000 : ℝ)^4951 ≤ (37848678606489/100000000000000 : ℝ)^3927 := by
    have hnat : (4627231039 : ℕ)^4951*100000000000000^3927 ≤ 37848678606489^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4627231039 10000000000 37848678606489 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3743461759/10000000000 : ℝ)^4951 ≤ (7243370047041/25000000000000 : ℝ)^3927 := by
    have hnat : (3743461759 : ℕ)^4951*25000000000000^3927 ≤ 7243370047041^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743461759 10000000000 7243370047041 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(833642061/2000000000 : ℝ), (4627231039/10000000000 : ℝ), (3743461759/10000000000 : ℝ)] ![(829446029887/2500000000000 : ℝ), (37848678606489/100000000000000 : ℝ), (7243370047041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(833642061/2000000000 : ℝ)|^4951 ≤ (829446029887/2500000000000 : ℝ)^3927
        have hw : |(833642061/2000000000 : ℝ)|=(833642061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4627231039/10000000000 : ℝ)|^4951 ≤ (37848678606489/100000000000000 : ℝ)^3927
        have hw : |(4627231039/10000000000 : ℝ)|=(4627231039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3743461759/10000000000 : ℝ)|^4951 ≤ (7243370047041/25000000000000 : ℝ)^3927
        have hw : |(3743461759/10000000000 : ℝ)|=(3743461759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1658_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5797/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9863/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (43/250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5797/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5797/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5797/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5797/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5797/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5797/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4997/100000 : ℝ) ^ (4947/1024 : ℝ) ≤ (51688473066151/100000000000000000000 : ℝ) := by
    have hpowers : (4997/100000 : ℝ)^4947 ≤ (51688473066151/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4997 : ℕ)^4947*100000000000000000000^1024 ≤ 51688473066151^1024*100000^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4997 100000 51688473066151 100000000000000000000 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4997/100000 : ℝ)) (X := (51688473066151/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5797/25000 : ℝ) ^ (4947/1024 : ℝ) ≤ (5363302187875451/6250000000000000000 : ℝ) := by
    have hpowers : (5797/25000 : ℝ)^4947 ≤ (5363302187875451/6250000000000000000 : ℝ)^1024 := by
      have hnat : (5797 : ℕ)^4947*6250000000000000000^1024 ≤ 5363302187875451^1024*25000^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5797 25000 5363302187875451 6250000000000000000 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5797/25000 : ℝ)) (X := (5363302187875451/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000051688473066151/50000000000000000000 : ℝ) ≤ (10000002139841307/10000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (50000051688473066151/50000000000000000000 : ℝ)^1024 ≤ (10000002139841307/10000000000000000 : ℝ)^4947 := by
      have hnat : (50000051688473066151 : ℕ)^1024*10000000000000000^4947 ≤ 10000002139841307^4947*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000051688473066151 50000000000000000000 10000002139841307 10000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002139841307/10000000000000000 : ℝ)) (X := (50000051688473066151/50000000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100085864523479073367/100000000000000000000 : ℝ) ≤ (2500444185126167/2500000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (100085864523479073367/100000000000000000000 : ℝ)^1024 ≤ (2500444185126167/2500000000000000 : ℝ)^4947 := by
      have hnat : (100085864523479073367 : ℕ)^1024*2500000000000000^4947 ≤ 2500444185126167^4947*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100085864523479073367 100000000000000000000 2500444185126167 2500000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500444185126167/2500000000000000 : ℝ)) (X := (100085864523479073367/100000000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3130363302187875451/3125000000000000000 : ℝ) ≤ (10003551341168029/10000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (3130363302187875451/3125000000000000000 : ℝ)^1024 ≤ (10003551341168029/10000000000000000 : ℝ)^4947 := by
      have hnat : (3130363302187875451 : ℕ)^1024*10000000000000000^4947 ≤ 10003551341168029^4947*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3130363302187875451 3125000000000000000 10003551341168029 10000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003551341168029/10000000000000000 : ℝ)) (X := (3130363302187875451/3125000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(51688473066151/100000000000000000000 : ℝ) ≤ ((181892303566823585803/181910000000000000000 : ℝ)+2*(1774600663361/1819100000000000 : ℝ)*(4997/100000 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (181892303566823585803/181910000000000000000 : ℝ)+2*(1774600663361/1819100000000000 : ℝ)*(4997/100000 : ℝ)=(10000002139841307/10000000000000000 : ℝ) by norm_num, show 1+2*(51688473066151/100000000000000000000 : ℝ)=(50000051688473066151/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5363302187875451/6250000000000000000 : ℝ)+(51688473066151/100000000000000000000 : ℝ) ≤ ((181892303566823585803/181910000000000000000 : ℝ)+(1774600663361/1819100000000000 : ℝ)*((5797/25000 : ℝ)+(4997/100000 : ℝ)))^(4947/1024 : ℝ) := by
    rw [show (181892303566823585803/181910000000000000000 : ℝ)+(1774600663361/1819100000000000 : ℝ)*((5797/25000 : ℝ)+(4997/100000 : ℝ))=(2500444185126167/2500000000000000 : ℝ) by norm_num, show 1+(5363302187875451/6250000000000000000 : ℝ)+(51688473066151/100000000000000000000 : ℝ)=(100085864523479073367/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5363302187875451/6250000000000000000 : ℝ) ≤ ((181892303566823585803/181910000000000000000 : ℝ)+2*(1774600663361/1819100000000000 : ℝ)*(5797/25000 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (181892303566823585803/181910000000000000000 : ℝ)+2*(1774600663361/1819100000000000 : ℝ)*(5797/25000 : ℝ)=(10003551341168029/10000000000000000 : ℝ) by norm_num, show 1+2*(5363302187875451/6250000000000000000 : ℝ)=(3130363302187875451/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (181892303566823585803/181910000000000000000 : ℝ)*(X 1 0+X 2 0)+(1774600663361/1819100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (4997/100000 : ℝ)) (hi := (5797/25000 : ℝ)) (c := (181892303566823585803/181910000000000000000 : ℝ)) (alpha := (1774600663361/1819100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (181892303566823585803/181910000000000000000 : ℝ)*(X 0 1+X 2 1)+(1774600663361/1819100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (4997/100000 : ℝ)) (hi := (5797/25000 : ℝ)) (c := (181892303566823585803/181910000000000000000 : ℝ)) (alpha := (1774600663361/1819100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (181892303566823585803/181910000000000000000 : ℝ)*(X 0 2+X 1 2)+(1774600663361/1819100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (4997/100000 : ℝ)) (hi := (5797/25000 : ℝ)) (c := (181892303566823585803/181910000000000000000 : ℝ)) (alpha := (1774600663361/1819100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1581338043/10000000000 : ℝ)*X 0 0+(5490395153/10000000000 : ℝ)*X 0 1+(1029050597/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358548191/10000000000 : ℝ)*X 1 0+(-1760587763/10000000000 : ℝ)*X 1 1+(1029050559/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679273821/5000000000 : ℝ)*X 2 0+(5145253377/10000000000 : ℝ)*X 2 1+(-1760587727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4167828431/10000000000 : ℝ)*X 0 0+(3734295573/10000000000 : ℝ)*X 0 1+(2318135457/5000000000 : ℝ)*X 0 2+(4167828431/10000000000 : ℝ)*X 1 0+(3734295573/10000000000 : ℝ)*X 1 1+(2318135457/5000000000 : ℝ)*X 1 2+(4167828431/10000000000 : ℝ)*X 2 0+(3734295573/10000000000 : ℝ)*X 2 1+(2318135457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-395371003/2500000000 : ℝ)*X 0 0+(5148712289/10000000000 : ℝ)*X 0 1+(2743443909/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266192437/10000000000 : ℝ)*X 1 0+(-354738233/2500000000 : ℝ)*X 1 1+(5486887871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2633096109/5000000000 : ℝ)*X 2 0+(5486888159/10000000000 : ℝ)*X 2 1+(-11085569/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((833642061/2000000000 : ℝ)*X 0 0+(4627231039/10000000000 : ℝ)*X 0 1+(3743461759/10000000000 : ℝ)*X 0 2+(833642061/2000000000 : ℝ)*X 1 0+(4627231039/10000000000 : ℝ)*X 1 1+(3743461759/10000000000 : ℝ)*X 1 2+(833642061/2000000000 : ℝ)*X 2 0+(4627231039/10000000000 : ℝ)*X 2 1+(3743461759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2179661624670808469697646083/284234375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1979771549/100000000000000 : ℝ)*(base19) + (97697217/6250000000000 : ℝ)*(base23) + (60492571/20000000000000 : ℝ)*(upper3) + (12835779/20000000000000 : ℝ)*(upper4) + (49036259/25000000000000 : ℝ)*(upper5) + (125190201366413/6250000000000 : ℝ)*(major0) + (125190201366413/6250000000000 : ℝ)*(major1) + (125190201366413/6250000000000 : ℝ)*(major2) + (1448688098191557/50000000000000 : ℝ)*(sp0) + (289739188505877/10000000000000 : ℝ)*(sp1) + (2897392301674847/100000000000000 : ℝ)*(sp2) + (1108684724011779/100000000000000 : ℝ)*(sp3) + (3533689441/20000000000000 : ℝ)*(sp4) + (7599265237/100000000000000 : ℝ)*(sp7) + (138586540409627/12500000000000 : ℝ)*(f.failure) + (2897393864830319/100000000000000 : ℝ)*(f.sum) + (17240350589841/11369375000000000000000000000 : ℝ)*base65 + (2485259565938302861/1136937500000000000000000000000000 : ℝ)*base68 + (4762583324545947139/1136937500000000000000000000000000 : ℝ)*base69 + (4625776504928134639/1136937500000000000000000000000000 : ℝ)*base71 + (77385999990003/22738750000000000000000000000 : ℝ)*base74 + (5354907103891572139/1136937500000000000000000000000000 : ℝ)*base75 + (2203672477961634639/1136937500000000000000000000000000 : ℝ)*base77 + (6479652211204697139/1136937500000000000000000000000000 : ℝ)*base79 + (14511208719743/5684687500000000000000000000 : ℝ)*base81 + (1300189/625000000000000000000 : ℝ)*base90 + (1300189/625000000000000000000 : ℝ)*base92 + (1300189/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34112758747471369801673157783/9095500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (163764371/20000000000000 : ℝ)*(base19) + (804651329/100000000000000 : ℝ)*(base23) + (8196459/20000000000000 : ℝ)*(upper2) + (57037221/50000000000000 : ℝ)*(upper3) + (82990559/100000000000000 : ℝ)*(upper5) + (2044279960901629/100000000000000 : ℝ)*(major0) + (2044279960901629/100000000000000 : ℝ)*(major1) + (2044279960901629/100000000000000 : ℝ)*(major2) + (7936578773/100000000000000 : ℝ)*(sp1) + (4851546353/50000000000000 : ℝ)*(sp2) + (1478521387907001/50000000000000 : ℝ)*(sp4) + (1478517010206687/50000000000000 : ℝ)*(sp5) + (2957032268069967/100000000000000 : ℝ)*(sp6) + (113151702097227/10000000000000 : ℝ)*(sp7) + (113151702097227/10000000000000 : ℝ)*(f.failure) + (1478521387907001/50000000000000 : ℝ)*(f.sum) + (152611207366261/90955000000000000000000000000 : ℝ)*base66 + (19538962991397126913/18191000000000000000000000000000000 : ℝ)*base68 + (94494823103875126913/18191000000000000000000000000000000 : ℝ)*base70 + (82688752502090126913/18191000000000000000000000000000000 : ℝ)*base72 + (41452950658601/22738750000000000000000000000 : ℝ)*base73 + (96588237071598126913/18191000000000000000000000000000000 : ℝ)*base76 + (71374204757697126913/18191000000000000000000000000000000 : ℝ)*base78 + (101957260259764126913/18191000000000000000000000000000000 : ℝ)*base80 + (185350213551649/90955000000000000000000000000 : ℝ)*base81 + (5246611/500000000000000000000 : ℝ)*base89 + (5246611/500000000000000000000 : ℝ)*base91 + (5246611/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1658_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5797/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9863/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (43/250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1658_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1658_s2_0 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-79495443/500000000 : ℝ)*x 0 + (2724139059/5000000000 : ℝ)*x 1 + (5181707077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79495443/500000000 : ℝ)^4951 ≤ (2460724424601/25000000000000 : ℝ)^3927 := by
    have hnat : (79495443 : ℕ)^4951*25000000000000^3927 ≤ 2460724424601^3927*500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79495443 500000000 2460724424601 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724139059/5000000000 : ℝ)^4951 ≤ (46503596253777/100000000000000 : ℝ)^3927 := by
    have hnat : (2724139059 : ℕ)^4951*100000000000000^3927 ≤ 46503596253777^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724139059 5000000000 46503596253777 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181707077/10000000000 : ℝ)^4951 ≤ (4365350603423/10000000000000 : ℝ)^3927 := by
    have hnat : (5181707077 : ℕ)^4951*10000000000000^3927 ≤ 4365350603423^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181707077 10000000000 4365350603423 10000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79495443/500000000 : ℝ), (2724139059/5000000000 : ℝ), (5181707077/10000000000 : ℝ)] ![(2460724424601/25000000000000 : ℝ), (46503596253777/100000000000000 : ℝ), (4365350603423/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79495443/500000000 : ℝ)|^4951 ≤ (2460724424601/25000000000000 : ℝ)^3927
        have hw : |(-79495443/500000000 : ℝ)|=(79495443/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724139059/5000000000 : ℝ)|^4951 ≤ (46503596253777/100000000000000 : ℝ)^3927
        have hw : |(2724139059/5000000000 : ℝ)|=(2724139059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181707077/10000000000 : ℝ)|^4951 ≤ (4365350603423/10000000000000 : ℝ)^3927
        have hw : |(5181707077/10000000000 : ℝ)|=(5181707077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s2_1 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336842791/2500000000 : ℝ)*x 0 + (-431794981/2500000000 : ℝ)*x 1 + (2590853717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336842791/2500000000 : ℝ)^4951 ≤ (5677544254463/12500000000000 : ℝ)^3927 := by
    have hnat : (1336842791 : ℕ)^4951*12500000000000^3927 ≤ 5677544254463^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336842791 2500000000 5677544254463 12500000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431794981/2500000000 : ℝ)^4951 ≤ (5463068061151/50000000000000 : ℝ)^3927 := by
    have hnat : (431794981 : ℕ)^4951*50000000000000^3927 ≤ 5463068061151^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431794981 2500000000 5463068061151 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590853717/5000000000 : ℝ)^4951 ≤ (43653509826039/100000000000000 : ℝ)^3927 := by
    have hnat : (2590853717 : ℕ)^4951*100000000000000^3927 ≤ 43653509826039^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590853717 5000000000 43653509826039 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336842791/2500000000 : ℝ), (-431794981/2500000000 : ℝ), (2590853717/5000000000 : ℝ)] ![(5677544254463/12500000000000 : ℝ), (5463068061151/50000000000000 : ℝ), (43653509826039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336842791/2500000000 : ℝ)|^4951 ≤ (5677544254463/12500000000000 : ℝ)^3927
        have hw : |(1336842791/2500000000 : ℝ)|=(1336842791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-431794981/2500000000 : ℝ)|^4951 ≤ (5463068061151/50000000000000 : ℝ)^3927
        have hw : |(-431794981/2500000000 : ℝ)|=(431794981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590853717/5000000000 : ℝ)|^4951 ≤ (43653509826039/100000000000000 : ℝ)^3927
        have hw : |(2590853717/5000000000 : ℝ)|=(2590853717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s2_2 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347370923/10000000000 : ℝ)*x 0 + (5181707307/10000000000 : ℝ)*x 1 + (-1727180417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347370923/10000000000 : ℝ)^4951 ≤ (363362811639/800000000000 : ℝ)^3927 := by
    have hnat : (5347370923 : ℕ)^4951*800000000000^3927 ≤ 363362811639^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347370923 10000000000 363362811639 800000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181707307/10000000000 : ℝ)^4951 ≤ (10913377119283/25000000000000 : ℝ)^3927 := by
    have hnat : (5181707307 : ℕ)^4951*25000000000000^3927 ≤ 10913377119283^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181707307 10000000000 10913377119283 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1727180417/10000000000 : ℝ)^4951 ≤ (2731535013563/25000000000000 : ℝ)^3927 := by
    have hnat : (1727180417 : ℕ)^4951*25000000000000^3927 ≤ 2731535013563^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727180417 10000000000 2731535013563 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347370923/10000000000 : ℝ), (5181707307/10000000000 : ℝ), (-1727180417/10000000000 : ℝ)] ![(363362811639/800000000000 : ℝ), (10913377119283/25000000000000 : ℝ), (2731535013563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347370923/10000000000 : ℝ)|^4951 ≤ (363362811639/800000000000 : ℝ)^3927
        have hw : |(5347370923/10000000000 : ℝ)|=(5347370923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181707307/10000000000 : ℝ)|^4951 ≤ (10913377119283/25000000000000 : ℝ)^3927
        have hw : |(5181707307/10000000000 : ℝ)|=(5181707307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1727180417/10000000000 : ℝ)|^4951 ≤ (2731535013563/25000000000000 : ℝ)^3927
        have hw : |(-1727180417/10000000000 : ℝ)|=(1727180417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s2_3 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4174229453/10000000000 : ℝ)*x 0 + (383632687/1000000000 : ℝ)*x 1 + (2266483229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4174229453/10000000000 : ℝ)^4951 ≤ (33238256543077/100000000000000 : ℝ)^3927 := by
    have hnat : (4174229453 : ℕ)^4951*100000000000000^3927 ≤ 33238256543077^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174229453 10000000000 33238256543077 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383632687/1000000000 : ℝ)^4951 ≤ (2988256792679/10000000000000 : ℝ)^3927 := by
    have hnat : (383632687 : ℕ)^4951*10000000000000^3927 ≤ 2988256792679^3927*1000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383632687 1000000000 2988256792679 10000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266483229/5000000000 : ℝ)^4951 ≤ (36879175504529/100000000000000 : ℝ)^3927 := by
    have hnat : (2266483229 : ℕ)^4951*100000000000000^3927 ≤ 36879175504529^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266483229 5000000000 36879175504529 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4174229453/10000000000 : ℝ), (383632687/1000000000 : ℝ), (2266483229/5000000000 : ℝ)] ![(33238256543077/100000000000000 : ℝ), (2988256792679/10000000000000 : ℝ), (36879175504529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4174229453/10000000000 : ℝ)|^4951 ≤ (33238256543077/100000000000000 : ℝ)^3927
        have hw : |(4174229453/10000000000 : ℝ)|=(4174229453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(383632687/1000000000 : ℝ)|^4951 ≤ (2988256792679/10000000000000 : ℝ)^3927
        have hw : |(383632687/1000000000 : ℝ)|=(383632687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2266483229/5000000000 : ℝ)|^4951 ≤ (36879175504529/100000000000000 : ℝ)^3927
        have hw : |(2266483229/5000000000 : ℝ)|=(2266483229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s2_4 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1589975823/10000000000 : ℝ)*x 0 + (5183776151/10000000000 : ℝ)*x 1 + (5446187153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1589975823/10000000000 : ℝ)^4951 ≤ (1968684071871/20000000000000 : ℝ)^3927 := by
    have hnat : (1589975823 : ℕ)^4951*20000000000000^3927 ≤ 1968684071871^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589975823 10000000000 1968684071871 20000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183776151/10000000000 : ℝ)^4951 ≤ (43675483465303/100000000000000 : ℝ)^3927 := by
    have hnat : (5183776151 : ℕ)^4951*100000000000000^3927 ≤ 43675483465303^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183776151 10000000000 43675483465303 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446187153/10000000000 : ℝ)^4951 ≤ (46481096160151/100000000000000 : ℝ)^3927 := by
    have hnat : (5446187153 : ℕ)^4951*100000000000000^3927 ≤ 46481096160151^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446187153 10000000000 46481096160151 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1589975823/10000000000 : ℝ), (5183776151/10000000000 : ℝ), (5446187153/10000000000 : ℝ)] ![(1968684071871/20000000000000 : ℝ), (43675483465303/100000000000000 : ℝ), (46481096160151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1589975823/10000000000 : ℝ)|^4951 ≤ (1968684071871/20000000000000 : ℝ)^3927
        have hw : |(-1589975823/10000000000 : ℝ)|=(1589975823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183776151/10000000000 : ℝ)|^4951 ≤ (43675483465303/100000000000000 : ℝ)^3927
        have hw : |(5183776151/10000000000 : ℝ)|=(5183776151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446187153/10000000000 : ℝ)|^4951 ≤ (46481096160151/100000000000000 : ℝ)^3927
        have hw : |(5446187153/10000000000 : ℝ)|=(5446187153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s2_5 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638044017/5000000000 : ℝ)*x 0 + (-731350353/5000000000 : ℝ)*x 1 + (272309327/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638044017/5000000000 : ℝ)^4951 ≤ (697786342297/1562500000000 : ℝ)^3927 := by
    have hnat : (2638044017 : ℕ)^4951*1562500000000^3927 ≤ 697786342297^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638044017 5000000000 697786342297 1562500000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (731350353/5000000000 : ℝ)^4951 ≤ (4430292259297/50000000000000 : ℝ)^3927 := by
    have hnat : (731350353 : ℕ)^4951*50000000000000^3927 ≤ 4430292259297^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731350353 5000000000 4430292259297 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272309327/500000000 : ℝ)^4951 ≤ (46481089564217/100000000000000 : ℝ)^3927 := by
    have hnat : (272309327 : ℕ)^4951*100000000000000^3927 ≤ 46481089564217^3927*500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272309327 500000000 46481089564217 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638044017/5000000000 : ℝ), (-731350353/5000000000 : ℝ), (272309327/500000000 : ℝ)] ![(697786342297/1562500000000 : ℝ), (4430292259297/50000000000000 : ℝ), (46481089564217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638044017/5000000000 : ℝ)|^4951 ≤ (697786342297/1562500000000 : ℝ)^3927
        have hw : |(2638044017/5000000000 : ℝ)|=(2638044017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-731350353/5000000000 : ℝ)|^4951 ≤ (4430292259297/50000000000000 : ℝ)^3927
        have hw : |(-731350353/5000000000 : ℝ)|=(731350353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272309327/500000000 : ℝ)|^4951 ≤ (46481089564217/100000000000000 : ℝ)^3927
        have hw : |(272309327/500000000 : ℝ)|=(272309327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s2_6 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276088331/10000000000 : ℝ)*x 0 + (1361546599/2500000000 : ℝ)*x 1 + (-1462700493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276088331/10000000000 : ℝ)^4951 ≤ (44658329076421/100000000000000 : ℝ)^3927 := by
    have hnat : (5276088331 : ℕ)^4951*100000000000000^3927 ≤ 44658329076421^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276088331 10000000000 44658329076421 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361546599/2500000000 : ℝ)^4951 ≤ (11620272003691/25000000000000 : ℝ)^3927 := by
    have hnat : (1361546599 : ℕ)^4951*25000000000000^3927 ≤ 11620272003691^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361546599 2500000000 11620272003691 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1462700493/10000000000 : ℝ)^4951 ≤ (8860582891853/100000000000000 : ℝ)^3927 := by
    have hnat : (1462700493 : ℕ)^4951*100000000000000^3927 ≤ 8860582891853^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1462700493 10000000000 8860582891853 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276088331/10000000000 : ℝ), (1361546599/2500000000 : ℝ), (-1462700493/10000000000 : ℝ)] ![(44658329076421/100000000000000 : ℝ), (11620272003691/25000000000000 : ℝ), (8860582891853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276088331/10000000000 : ℝ)|^4951 ≤ (44658329076421/100000000000000 : ℝ)^3927
        have hw : |(5276088331/10000000000 : ℝ)|=(5276088331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361546599/2500000000 : ℝ)|^4951 ≤ (11620272003691/25000000000000 : ℝ)^3927
        have hw : |(1361546599/2500000000 : ℝ)|=(1361546599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1462700493/10000000000 : ℝ)|^4951 ≤ (8860582891853/100000000000000 : ℝ)^3927
        have hw : |(-1462700493/10000000000 : ℝ)|=(1462700493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s2_7 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (521800791/1250000000 : ℝ)*x 0 + (4527560227/10000000000 : ℝ)*x 1 + (1920895409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521800791/1250000000 : ℝ)^4951 ≤ (16620016107637/50000000000000 : ℝ)^3927 := by
    have hnat : (521800791 : ℕ)^4951*50000000000000^3927 ≤ 16620016107637^3927*1250000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521800791 1250000000 16620016107637 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4527560227/10000000000 : ℝ)^4951 ≤ (1841186554737/5000000000000 : ℝ)^3927 := by
    have hnat : (4527560227 : ℕ)^4951*5000000000000^3927 ≤ 1841186554737^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527560227 10000000000 1841186554737 5000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1920895409/5000000000 : ℝ)^4951 ≤ (29936236679829/100000000000000 : ℝ)^3927 := by
    have hnat : (1920895409 : ℕ)^4951*100000000000000^3927 ≤ 29936236679829^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920895409 5000000000 29936236679829 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521800791/1250000000 : ℝ), (4527560227/10000000000 : ℝ), (1920895409/5000000000 : ℝ)] ![(16620016107637/50000000000000 : ℝ), (1841186554737/5000000000000 : ℝ), (29936236679829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521800791/1250000000 : ℝ)|^4951 ≤ (16620016107637/50000000000000 : ℝ)^3927
        have hw : |(521800791/1250000000 : ℝ)|=(521800791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4527560227/10000000000 : ℝ)|^4951 ≤ (1841186554737/5000000000000 : ℝ)^3927
        have hw : |(4527560227/10000000000 : ℝ)|=(4527560227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1920895409/5000000000 : ℝ)|^4951 ≤ (29936236679829/100000000000000 : ℝ)^3927
        have hw : |(1920895409/5000000000 : ℝ)|=(1920895409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1658_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (43/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9863/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (213/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (102/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (43/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9863/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (43/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9863/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (43/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9863/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (43/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9863/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (43/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9863/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (43/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9863/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9863/100000 : ℝ) ^ (4947/1024 : ℝ) ≤ (690196302267239/50000000000000000000 : ℝ) := by
    have hpowers : (9863/100000 : ℝ)^4947 ≤ (690196302267239/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9863 : ℕ)^4947*50000000000000000000^1024 ≤ 690196302267239^1024*100000^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9863 100000 690196302267239 50000000000000000000 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9863/100000 : ℝ)) (X := (690196302267239/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (43/250 : ℝ) ^ (4947/1024 : ℝ) ≤ (20267310450125709/100000000000000000000 : ℝ) := by
    have hpowers : (43/250 : ℝ)^4947 ≤ (20267310450125709/100000000000000000000 : ℝ)^1024 := by
      have hnat : (43 : ℕ)^4947*100000000000000000000^1024 ≤ 20267310450125709^1024*250^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43 250 20267310450125709 100000000000000000000 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43/250 : ℝ)) (X := (20267310450125709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000690196302267239/25000000000000000000 : ℝ) ≤ (10000057146009867/10000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (25000690196302267239/25000000000000000000 : ℝ)^1024 ≤ (10000057146009867/10000000000000000 : ℝ)^4947 := by
      have hnat : (25000690196302267239 : ℕ)^1024*10000000000000000^4947 ≤ 10000057146009867^4947*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000690196302267239 25000000000000000000 10000057146009867 10000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000057146009867/10000000000000000 : ℝ)) (X := (25000690196302267239/25000000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100021647703054660187/100000000000000000000 : ℝ) ≤ (5000224028153179/5000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (100021647703054660187/100000000000000000000 : ℝ)^1024 ≤ (5000224028153179/5000000000000000 : ℝ)^4947 := by
      have hnat : (100021647703054660187 : ℕ)^1024*5000000000000000^4947 ≤ 5000224028153179^4947*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021647703054660187 100000000000000000000 5000224028153179 5000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000224028153179/5000000000000000 : ℝ)) (X := (100021647703054660187/100000000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020267310450125709/50000000000000000000 : ℝ) ≤ (10000838966602849/10000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (50020267310450125709/50000000000000000000 : ℝ)^1024 ≤ (10000838966602849/10000000000000000 : ℝ)^4947 := by
      have hnat : (50020267310450125709 : ℕ)^1024*10000000000000000^4947 ≤ 10000838966602849^4947*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020267310450125709 50000000000000000000 10000838966602849 10000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000838966602849/10000000000000000 : ℝ)) (X := (50020267310450125709/50000000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(690196302267239/50000000000000000000 : ℝ) ≤ ((6669337107615073883/6670000000000000000 : ℝ)+2*(35537299681/66700000000000 : ℝ)*(9863/100000 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (6669337107615073883/6670000000000000000 : ℝ)+2*(35537299681/66700000000000 : ℝ)*(9863/100000 : ℝ)=(10000057146009867/10000000000000000 : ℝ) by norm_num, show 1+2*(690196302267239/50000000000000000000 : ℝ)=(25000690196302267239/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20267310450125709/100000000000000000000 : ℝ)+(690196302267239/50000000000000000000 : ℝ) ≤ ((6669337107615073883/6670000000000000000 : ℝ)+(35537299681/66700000000000 : ℝ)*((43/250 : ℝ)+(9863/100000 : ℝ)))^(4947/1024 : ℝ) := by
    rw [show (6669337107615073883/6670000000000000000 : ℝ)+(35537299681/66700000000000 : ℝ)*((43/250 : ℝ)+(9863/100000 : ℝ))=(5000224028153179/5000000000000000 : ℝ) by norm_num, show 1+(20267310450125709/100000000000000000000 : ℝ)+(690196302267239/50000000000000000000 : ℝ)=(100021647703054660187/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20267310450125709/100000000000000000000 : ℝ) ≤ ((6669337107615073883/6670000000000000000 : ℝ)+2*(35537299681/66700000000000 : ℝ)*(43/250 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (6669337107615073883/6670000000000000000 : ℝ)+2*(35537299681/66700000000000 : ℝ)*(43/250 : ℝ)=(10000838966602849/10000000000000000 : ℝ) by norm_num, show 1+2*(20267310450125709/100000000000000000000 : ℝ)=(50020267310450125709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6669337107615073883/6670000000000000000 : ℝ)*(X 1 0+X 2 0)+(35537299681/66700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (9863/100000 : ℝ)) (hi := (43/250 : ℝ)) (c := (6669337107615073883/6670000000000000000 : ℝ)) (alpha := (35537299681/66700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6669337107615073883/6670000000000000000 : ℝ)*(X 0 1+X 2 1)+(35537299681/66700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (9863/100000 : ℝ)) (hi := (43/250 : ℝ)) (c := (6669337107615073883/6670000000000000000 : ℝ)) (alpha := (35537299681/66700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6669337107615073883/6670000000000000000 : ℝ)*(X 0 2+X 1 2)+(35537299681/66700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (9863/100000 : ℝ)) (hi := (43/250 : ℝ)) (c := (6669337107615073883/6670000000000000000 : ℝ)) (alpha := (35537299681/66700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-79495443/500000000 : ℝ)*X 0 0+(2724139059/5000000000 : ℝ)*X 0 1+(5181707077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336842791/2500000000 : ℝ)*X 1 0+(-431794981/2500000000 : ℝ)*X 1 1+(2590853717/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347370923/10000000000 : ℝ)*X 2 0+(5181707307/10000000000 : ℝ)*X 2 1+(-1727180417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4174229453/10000000000 : ℝ)*X 0 0+(383632687/1000000000 : ℝ)*X 0 1+(2266483229/5000000000 : ℝ)*X 0 2+(4174229453/10000000000 : ℝ)*X 1 0+(383632687/1000000000 : ℝ)*X 1 1+(2266483229/5000000000 : ℝ)*X 1 2+(4174229453/10000000000 : ℝ)*X 2 0+(383632687/1000000000 : ℝ)*X 2 1+(2266483229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1589975823/10000000000 : ℝ)*X 0 0+(5183776151/10000000000 : ℝ)*X 0 1+(5446187153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638044017/5000000000 : ℝ)*X 1 0+(-731350353/5000000000 : ℝ)*X 1 1+(272309327/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276088331/10000000000 : ℝ)*X 2 0+(1361546599/2500000000 : ℝ)*X 2 1+(-1462700493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((521800791/1250000000 : ℝ)*X 0 0+(4527560227/10000000000 : ℝ)*X 0 1+(1920895409/5000000000 : ℝ)*X 0 2+(521800791/1250000000 : ℝ)*X 1 0+(4527560227/10000000000 : ℝ)*X 1 1+(1920895409/5000000000 : ℝ)*X 1 2+(521800791/1250000000 : ℝ)*X 2 0+(4527560227/10000000000 : ℝ)*X 2 1+(1920895409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4556812967463046234297482957/333500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (428725691/25000000000000 : ℝ)*(base19) + (1539659553/100000000000000 : ℝ)*(base23) + (447756543/100000000000000 : ℝ)*(upper3) + (3300481/100000000000000 : ℝ)*(upper4) + (29008187/100000000000000 : ℝ)*(upper5) + (2593435952954753/100000000000000 : ℝ)*(major0) + (2593435952954753/100000000000000 : ℝ)*(major1) + (1296717976477377/50000000000000 : ℝ)*(major2) + (3751375045943877/100000000000000 : ℝ)*(sp0) + (468924088389437/12500000000000 : ℝ)*(sp1) + (937848220589677/25000000000000 : ℝ)*(sp2) + (143546823144299/10000000000000 : ℝ)*(sp3) + (1211004649/6250000000000 : ℝ)*(sp4) + (8796994677/100000000000000 : ℝ)*(sp7) + (1435477028437667/100000000000000 : ℝ)*(f.failure) + (3751394422018261/100000000000000 : ℝ)*(f.sum) + (494705300313/6670000000000000000000000000 : ℝ)*base66 + (1540992636115415899/667000000000000000000000000000000 : ℝ)*base67 + (972103467708194891/333500000000000000000000000000000 : ℝ)*base69 + (6967034020308415899/667000000000000000000000000000000 : ℝ)*base71 + (18176502965017/6670000000000000000000000000 : ℝ)*base73 + (5303971324877694891/333500000000000000000000000000000 : ℝ)*base75 + (150716936791735031/23000000000000000000000000000000 : ℝ)*base77 + (111257302683264969/23000000000000000000000000000000 : ℝ)*base80 + (146090058833/115000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (13352469/5000000000000000000000 : ℝ)*base90 + (13352469/5000000000000000000000 : ℝ)*base92 + (63352469/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (906760794632665955517798093/83375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (550208731/50000000000000 : ℝ)*(base19) + (474506573/25000000000000 : ℝ)*(base23) + (32615391/50000000000000 : ℝ)*(upper3) + (254505077/100000000000000 : ℝ)*(lower4) + (16999817/10000000000000 : ℝ)*(upper5) + (658628817365319/25000000000000 : ℝ)*(major0) + (658628817365319/25000000000000 : ℝ)*(major1) + (658628817365319/25000000000000 : ℝ)*(major2) + (7648082699/100000000000000 : ℝ)*(sp1) + (1887857909/12500000000000 : ℝ)*(sp2) + (1905407792129589/50000000000000 : ℝ)*(sp4) + (476350854469877/12500000000000 : ℝ)*(sp5) + (1905399291684807/50000000000000 : ℝ)*(sp6) + (1458214592140311/100000000000000 : ℝ)*(sp7) + (1458214592140311/100000000000000 : ℝ)*(f.failure) + (1905407792129589/50000000000000 : ℝ)*(f.sum) + (8586836225617/1667500000000000000000000000 : ℝ)*base66 + (875465634795486323/166750000000000000000000000000000 : ℝ)*base68 + (757445013475236323/166750000000000000000000000000000 : ℝ)*base70 + (1489292346938236323/166750000000000000000000000000000 : ℝ)*base72 + (1445712885581/3335000000000000000000000000 : ℝ)*base73 + (195829141206236323/166750000000000000000000000000000 : ℝ)*base76 + (2102550174280736323/166750000000000000000000000000000 : ℝ)*base78 + (680640899442986323/166750000000000000000000000000000 : ℝ)*base80 + (3356183311459/833750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (52767423/5000000000000000000000 : ℝ)*base89 + (52767423/5000000000000000000000 : ℝ)*base91 + (52767423/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1658_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (43/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9863/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (102/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1658_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1658_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (102/625 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1658_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1658_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1658_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (102/625 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1658_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
