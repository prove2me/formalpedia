-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1317_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:16.481106+00:00
-- url     : https://prove2.me/submissions/122ff57f-e37d-4d8d-b7de-d2bab371230d

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
theorem support_rectangle_w1317_s0_0 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1824018113/10000000000 : ℝ)*x 0 + (6007784543/10000000000 : ℝ)*x 1 + (4804909271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1824018113/10000000000 : ℝ)^4277 ≤ (5338032487017/50000000000000 : ℝ)^3253 := by
    have hnat : (1824018113 : ℕ)^4277*50000000000000^3253 ≤ 5338032487017^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824018113 10000000000 5338032487017 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6007784543/10000000000 : ℝ)^4277 ≤ (25587429021639/50000000000000 : ℝ)^3253 := by
    have hnat : (6007784543 : ℕ)^4277*50000000000000^3253 ≤ 25587429021639^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6007784543 10000000000 25587429021639 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4804909271/10000000000 : ℝ)^4277 ≤ (1907453848129/5000000000000 : ℝ)^3253 := by
    have hnat : (4804909271 : ℕ)^4277*5000000000000^3253 ≤ 1907453848129^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4804909271 10000000000 1907453848129 5000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1824018113/10000000000 : ℝ), (6007784543/10000000000 : ℝ), (4804909271/10000000000 : ℝ)] ![(5338032487017/50000000000000 : ℝ), (25587429021639/50000000000000 : ℝ), (1907453848129/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1824018113/10000000000 : ℝ)|^4277 ≤ (5338032487017/50000000000000 : ℝ)^3253
        have hw : |(-1824018113/10000000000 : ℝ)|=(1824018113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6007784543/10000000000 : ℝ)|^4277 ≤ (25587429021639/50000000000000 : ℝ)^3253
        have hw : |(6007784543/10000000000 : ℝ)|=(6007784543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4804909271/10000000000 : ℝ)|^4277 ≤ (1907453848129/5000000000000 : ℝ)^3253
        have hw : |(4804909271/10000000000 : ℝ)|=(4804909271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s0_1 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5504614461/10000000000 : ℝ)*x 0 + (-2508978901/10000000000 : ℝ)*x 1 + (192196373/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5504614461/10000000000 : ℝ)^4277 ≤ (45615377756591/100000000000000 : ℝ)^3253 := by
    have hnat : (5504614461 : ℕ)^4277*100000000000000^3253 ≤ 45615377756591^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504614461 10000000000 45615377756591 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2508978901/10000000000 : ℝ)^4277 ≤ (3247108941299/20000000000000 : ℝ)^3253 := by
    have hnat : (2508978901 : ℕ)^4277*20000000000000^3253 ≤ 3247108941299^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508978901 10000000000 3247108941299 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192196373/400000000 : ℝ)^4277 ≤ (953726938157/2500000000000 : ℝ)^3253 := by
    have hnat : (192196373 : ℕ)^4277*2500000000000^3253 ≤ 953726938157^3253*400000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192196373 400000000 953726938157 2500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5504614461/10000000000 : ℝ), (-2508978901/10000000000 : ℝ), (192196373/400000000 : ℝ)] ![(45615377756591/100000000000000 : ℝ), (3247108941299/20000000000000 : ℝ), (953726938157/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5504614461/10000000000 : ℝ)|^4277 ≤ (45615377756591/100000000000000 : ℝ)^3253
        have hw : |(5504614461/10000000000 : ℝ)|=(5504614461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2508978901/10000000000 : ℝ)|^4277 ≤ (3247108941299/20000000000000 : ℝ)^3253
        have hw : |(-2508978901/10000000000 : ℝ)|=(2508978901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(192196373/400000000 : ℝ)|^4277 ≤ (953726938157/2500000000000 : ℝ)^3253
        have hw : |(192196373/400000000 : ℝ)|=(192196373/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s0_2 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5504613689/10000000000 : ℝ)*x 0 + (4804909827/10000000000 : ℝ)*x 1 + (-313622409/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5504613689/10000000000 : ℝ)^4277 ≤ (45615369345413/100000000000000 : ℝ)^3253 := by
    have hnat : (5504613689 : ℕ)^4277*100000000000000^3253 ≤ 45615369345413^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504613689 10000000000 45615369345413 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4804909827/10000000000 : ℝ)^4277 ≤ (38149082766599/100000000000000 : ℝ)^3253 := by
    have hnat : (4804909827 : ℕ)^4277*100000000000000^3253 ≤ 38149082766599^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4804909827 10000000000 38149082766599 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313622409/1250000000 : ℝ)^4277 ≤ (3247109572589/20000000000000 : ℝ)^3253 := by
    have hnat : (313622409 : ℕ)^4277*20000000000000^3253 ≤ 3247109572589^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313622409 1250000000 3247109572589 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5504613689/10000000000 : ℝ), (4804909827/10000000000 : ℝ), (-313622409/1250000000 : ℝ)] ![(45615369345413/100000000000000 : ℝ), (38149082766599/100000000000000 : ℝ), (3247109572589/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5504613689/10000000000 : ℝ)|^4277 ≤ (45615369345413/100000000000000 : ℝ)^3253
        have hw : |(5504613689/10000000000 : ℝ)|=(5504613689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4804909827/10000000000 : ℝ)|^4277 ≤ (38149082766599/100000000000000 : ℝ)^3253
        have hw : |(4804909827/10000000000 : ℝ)|=(4804909827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-313622409/1250000000 : ℝ)|^4277 ≤ (3247109572589/20000000000000 : ℝ)^3253
        have hw : |(-313622409/1250000000 : ℝ)|=(313622409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s0_3 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4182513801/10000000000 : ℝ)*x 0 + (3107901461/10000000000 : ℝ)*x 1 + (5603731229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182513801/10000000000 : ℝ)^4277 ≤ (7947143341399/25000000000000 : ℝ)^3253 := by
    have hnat : (4182513801 : ℕ)^4277*25000000000000^3253 ≤ 7947143341399^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182513801 10000000000 7947143341399 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3107901461/10000000000 : ℝ)^4277 ≤ (21513093029601/100000000000000 : ℝ)^3253 := by
    have hnat : (3107901461 : ℕ)^4277*100000000000000^3253 ≤ 21513093029601^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107901461 10000000000 21513093029601 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5603731229/10000000000 : ℝ)^4277 ≤ (46698333592447/100000000000000 : ℝ)^3253 := by
    have hnat : (5603731229 : ℕ)^4277*100000000000000^3253 ≤ 46698333592447^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5603731229 10000000000 46698333592447 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182513801/10000000000 : ℝ), (3107901461/10000000000 : ℝ), (5603731229/10000000000 : ℝ)] ![(7947143341399/25000000000000 : ℝ), (21513093029601/100000000000000 : ℝ), (46698333592447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182513801/10000000000 : ℝ)|^4277 ≤ (7947143341399/25000000000000 : ℝ)^3253
        have hw : |(4182513801/10000000000 : ℝ)|=(4182513801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3107901461/10000000000 : ℝ)|^4277 ≤ (21513093029601/100000000000000 : ℝ)^3253
        have hw : |(3107901461/10000000000 : ℝ)|=(3107901461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5603731229/10000000000 : ℝ)|^4277 ≤ (46698333592447/100000000000000 : ℝ)^3253
        have hw : |(5603731229/10000000000 : ℝ)|=(5603731229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s0_4 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1828607399/10000000000 : ℝ)*x 0 + (12089781/25000000 : ℝ)*x 1 + (5975675887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1828607399/10000000000 : ℝ)^4277 ≤ (41841389981/390625000000 : ℝ)^3253 := by
    have hnat : (1828607399 : ℕ)^4277*390625000000^3253 ≤ 41841389981^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828607399 10000000000 41841389981 390625000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12089781/25000000 : ℝ)^4277 ≤ (38473043190043/100000000000000 : ℝ)^3253 := by
    have hnat : (12089781 : ℕ)^4277*100000000000000^3253 ≤ 38473043190043^3253*25000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12089781 25000000 38473043190043 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5975675887/10000000000 : ℝ)^4277 ≤ (25407780482009/50000000000000 : ℝ)^3253 := by
    have hnat : (5975675887 : ℕ)^4277*50000000000000^3253 ≤ 25407780482009^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5975675887 10000000000 25407780482009 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1828607399/10000000000 : ℝ), (12089781/25000000 : ℝ), (5975675887/10000000000 : ℝ)] ![(41841389981/390625000000 : ℝ), (38473043190043/100000000000000 : ℝ), (25407780482009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1828607399/10000000000 : ℝ)|^4277 ≤ (41841389981/390625000000 : ℝ)^3253
        have hw : |(-1828607399/10000000000 : ℝ)|=(1828607399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12089781/25000000 : ℝ)|^4277 ≤ (38473043190043/100000000000000 : ℝ)^3253
        have hw : |(12089781/25000000 : ℝ)|=(12089781/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5975675887/10000000000 : ℝ)|^4277 ≤ (25407780482009/50000000000000 : ℝ)^3253
        have hw : |(5975675887/10000000000 : ℝ)|=(5975675887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s0_5 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5176959339/10000000000 : ℝ)*x 0 + (-669106609/5000000000 : ℝ)*x 1 + (597567581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5176959339/10000000000 : ℝ)^4277 ≤ (4207938550299/10000000000000 : ℝ)^3253 := by
    have hnat : (5176959339 : ℕ)^4277*10000000000000^3253 ≤ 4207938550299^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176959339 10000000000 4207938550299 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (669106609/5000000000 : ℝ)^4277 ≤ (3552527192013/50000000000000 : ℝ)^3253 := by
    have hnat : (669106609 : ℕ)^4277*50000000000000^3253 ≤ 3552527192013^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669106609 5000000000 3552527192013 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (597567581/1000000000 : ℝ)^4277 ≤ (6351945012889/12500000000000 : ℝ)^3253 := by
    have hnat : (597567581 : ℕ)^4277*12500000000000^3253 ≤ 6351945012889^3253*1000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597567581 1000000000 6351945012889 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5176959339/10000000000 : ℝ), (-669106609/5000000000 : ℝ), (597567581/1000000000 : ℝ)] ![(4207938550299/10000000000000 : ℝ), (3552527192013/50000000000000 : ℝ), (6351945012889/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5176959339/10000000000 : ℝ)|^4277 ≤ (4207938550299/10000000000000 : ℝ)^3253
        have hw : |(5176959339/10000000000 : ℝ)|=(5176959339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-669106609/5000000000 : ℝ)|^4277 ≤ (3552527192013/50000000000000 : ℝ)^3253
        have hw : |(-669106609/5000000000 : ℝ)|=(669106609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(597567581/1000000000 : ℝ)|^4277 ≤ (6351945012889/12500000000000 : ℝ)^3253
        have hw : |(597567581/1000000000 : ℝ)|=(597567581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s0_6 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8088999/15625000 : ℝ)*x 0 + (2987837927/5000000000 : ℝ)*x 1 + (-669106557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8088999/15625000 : ℝ)^4277 ≤ (21039692863707/50000000000000 : ℝ)^3253 := by
    have hnat : (8088999 : ℕ)^4277*50000000000000^3253 ≤ 21039692863707^3253*15625000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8088999 15625000 21039692863707 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2987837927/5000000000 : ℝ)^4277 ≤ (50815560595059/100000000000000 : ℝ)^3253 := by
    have hnat : (2987837927 : ℕ)^4277*100000000000000^3253 ≤ 50815560595059^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2987837927 5000000000 50815560595059 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (669106557/5000000000 : ℝ)^4277 ≤ (1776263414509/25000000000000 : ℝ)^3253 := by
    have hnat : (669106557 : ℕ)^4277*25000000000000^3253 ≤ 1776263414509^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669106557 5000000000 1776263414509 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8088999/15625000 : ℝ), (2987837927/5000000000 : ℝ), (-669106557/5000000000 : ℝ)] ![(21039692863707/50000000000000 : ℝ), (50815560595059/100000000000000 : ℝ), (1776263414509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8088999/15625000 : ℝ)|^4277 ≤ (21039692863707/50000000000000 : ℝ)^3253
        have hw : |(8088999/15625000 : ℝ)|=(8088999/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2987837927/5000000000 : ℝ)|^4277 ≤ (50815560595059/100000000000000 : ℝ)^3253
        have hw : |(2987837927/5000000000 : ℝ)|=(2987837927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-669106557/5000000000 : ℝ)|^4277 ≤ (1776263414509/25000000000000 : ℝ)^3253
        have hw : |(-669106557/5000000000 : ℝ)|=(669106557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s0_7 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4192035359/10000000000 : ℝ)*x 0 + (276970191/500000000 : ℝ)*x 1 + (1587261299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192035359/10000000000 : ℝ)^4277 ≤ (63767509651/200000000000 : ℝ)^3253 := by
    have hnat : (4192035359 : ℕ)^4277*200000000000^3253 ≤ 63767509651^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192035359 10000000000 63767509651 200000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276970191/500000000 : ℝ)^4277 ≤ (45994795077187/100000000000000 : ℝ)^3253 := by
    have hnat : (276970191 : ℕ)^4277*100000000000000^3253 ≤ 45994795077187^3253*500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276970191 500000000 45994795077187 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1587261299/5000000000 : ℝ)^4277 ≤ (2212145008709/10000000000000 : ℝ)^3253 := by
    have hnat : (1587261299 : ℕ)^4277*10000000000000^3253 ≤ 2212145008709^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587261299 5000000000 2212145008709 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192035359/10000000000 : ℝ), (276970191/500000000 : ℝ), (1587261299/5000000000 : ℝ)] ![(63767509651/200000000000 : ℝ), (45994795077187/100000000000000 : ℝ), (2212145008709/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192035359/10000000000 : ℝ)|^4277 ≤ (63767509651/200000000000 : ℝ)^3253
        have hw : |(4192035359/10000000000 : ℝ)|=(4192035359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(276970191/500000000 : ℝ)|^4277 ≤ (45994795077187/100000000000000 : ℝ)^3253
        have hw : |(276970191/500000000 : ℝ)|=(276970191/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1587261299/5000000000 : ℝ)|^4277 ≤ (2212145008709/10000000000000 : ℝ)^3253
        have hw : |(1587261299/5000000000 : ℝ)|=(1587261299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1317_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (49/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6763/25000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (1069/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1069 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1069*1^256 ≤ 0^256*1^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1069/256 : ℝ) ≤ (2179162281220818633/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1069 ≤ (2179162281220818633/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1069*100000000000000000000^256 ≤ 2179162281220818633^256*5^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2179162281220818633 100000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2179162281220818633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1069 := by
      have hnat : (1 : ℕ)^256*1^1069 ≤ 1^1069*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (102179162281220818633/100000000000000000000 : ℝ) ≤ (10051758748338259/10000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (102179162281220818633/100000000000000000000 : ℝ)^256 ≤ (10051758748338259/10000000000000000 : ℝ)^1069 := by
      have hnat : (102179162281220818633 : ℕ)^256*10000000000000000^1069 ≤ 10051758748338259^1069*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102179162281220818633 100000000000000000000 10051758748338259 10000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10051758748338259/10000000000000000 : ℝ)) (X := (102179162281220818633/100000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (52179162281220818633/50000000000000000000 : ℝ) ≤ (5051758748338259/5000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (52179162281220818633/50000000000000000000 : ℝ)^256 ≤ (5051758748338259/5000000000000000 : ℝ)^1069 := by
      have hnat : (52179162281220818633 : ℕ)^256*5000000000000000^1069 ≤ 5051758748338259^1069*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52179162281220818633 50000000000000000000 5051758748338259 5000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5051758748338259/5000000000000000 : ℝ)) (X := (52179162281220818633/50000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(51758748338259/4000000000000000 : ℝ)*(0 : ℝ))^(1069/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(51758748338259/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2179162281220818633/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(51758748338259/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1069/256 : ℝ) := by
    rw [show (1 : ℝ)+(51758748338259/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10051758748338259/10000000000000000 : ℝ) by norm_num, show 1+(2179162281220818633/100000000000000000000 : ℝ)+(0 : ℝ)=(102179162281220818633/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2179162281220818633/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(51758748338259/4000000000000000 : ℝ)*(2/5 : ℝ))^(1069/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(51758748338259/4000000000000000 : ℝ)*(2/5 : ℝ)=(5051758748338259/5000000000000000 : ℝ) by norm_num, show 1+2*(2179162281220818633/100000000000000000000 : ℝ)=(52179162281220818633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(51758748338259/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51758748338259/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(51758748338259/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51758748338259/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(51758748338259/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51758748338259/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1824018113/10000000000 : ℝ)*X 0 0+(6007784543/10000000000 : ℝ)*X 0 1+(4804909271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5504614461/10000000000 : ℝ)*X 1 0+(-2508978901/10000000000 : ℝ)*X 1 1+(192196373/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5504613689/10000000000 : ℝ)*X 2 0+(4804909827/10000000000 : ℝ)*X 2 1+(-313622409/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4182513801/10000000000 : ℝ)*X 0 0+(3107901461/10000000000 : ℝ)*X 0 1+(5603731229/10000000000 : ℝ)*X 0 2+(4182513801/10000000000 : ℝ)*X 1 0+(3107901461/10000000000 : ℝ)*X 1 1+(5603731229/10000000000 : ℝ)*X 1 2+(4182513801/10000000000 : ℝ)*X 2 0+(3107901461/10000000000 : ℝ)*X 2 1+(5603731229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1828607399/10000000000 : ℝ)*X 0 0+(12089781/25000000 : ℝ)*X 0 1+(5975675887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5176959339/10000000000 : ℝ)*X 1 0+(-669106609/5000000000 : ℝ)*X 1 1+(597567581/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((8088999/15625000 : ℝ)*X 2 0+(2987837927/5000000000 : ℝ)*X 2 1+(-669106557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4192035359/10000000000 : ℝ)*X 0 0+(276970191/500000000 : ℝ)*X 0 1+(1587261299/5000000000 : ℝ)*X 0 2+(4192035359/10000000000 : ℝ)*X 1 0+(276970191/500000000 : ℝ)*X 1 1+(1587261299/5000000000 : ℝ)*X 1 2+(4192035359/10000000000 : ℝ)*X 2 0+(276970191/500000000 : ℝ)*X 2 1+(1587261299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (212747223159238913926839/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35166409/50000000000000 : ℝ)*(base1) + (1118771019/100000000000000 : ℝ)*(base19) + (25054447/2500000000000 : ℝ)*(base23) + (175414981/100000000000000 : ℝ)*(upper3) + (350873/800000000000 : ℝ)*(upper5) + (154002540221931/25000000000000 : ℝ)*(major0) + (154002540221931/25000000000000 : ℝ)*(major1) + (154002540221931/25000000000000 : ℝ)*(major2) + (831345373605129/100000000000000 : ℝ)*(sp0) + (207836850068021/25000000000000 : ℝ)*(sp1) + (103918439608153/12500000000000 : ℝ)*(sp2) + (80133956128271/20000000000000 : ℝ)*(sp3) + (401971349/12500000000000 : ℝ)*(sp4) + (1809926683/100000000000000 : ℝ)*(sp7) + (50083957612607/12500000000000 : ℝ)*(f.failure) + (831348519043103/100000000000000 : ℝ)*(f.sum) + (19416330191871/50000000000000000000000000000 : ℝ)*base66 + (812556261958129/100000000000000000000000000000 : ℝ)*base67 + (589195198958129/100000000000000000000000000000 : ℝ)*base69 + (418612190558129/100000000000000000000000000000 : ℝ)*base71 + (134137866608129/50000000000000000000000000000 : ℝ)*base73 + (484171215258129/100000000000000000000000000000 : ℝ)*base75 + (270867729358129/100000000000000000000000000000 : ℝ)*base77 + (212425178141871/100000000000000000000000000000 : ℝ)*base80 + (79184278108129/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (330067/62500000000000000000 : ℝ)*base90 + (330067/62500000000000000000 : ℝ)*base92 + (330067/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222870545758963403585673/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1063577357/100000000000000 : ℝ)*(base19) + (539172067/50000000000000 : ℝ)*(base23) + (17674157/50000000000000 : ℝ)*(base32) + (145191321/100000000000000 : ℝ)*(upper3) + (11092111/10000000000000 : ℝ)*(upper5) + (325057290309717/50000000000000 : ℝ)*(major0) + (325057290309717/50000000000000 : ℝ)*(major1) + (325057290309717/50000000000000 : ℝ)*(major2) + (2358035569/100000000000000 : ℝ)*(sp1) + (316890589/12500000000000 : ℝ)*(sp2) + (219343701127887/25000000000000 : ℝ)*(sp4) + (877371382898621/100000000000000 : ℝ)*(sp5) + (438685595521351/50000000000000 : ℝ)*(sp6) + (422854172798633/100000000000000 : ℝ)*(sp7) + (422854208146947/100000000000000 : ℝ)*(f.failure) + (219343701127887/25000000000000 : ℝ)*(f.sum) + (11205131062703/100000000000000000000000000000 : ℝ)*base65 + (2108642538562703/200000000000000000000000000000 : ℝ)*base67 + (326386868562703/200000000000000000000000000000 : ℝ)*base69 + (1224357375562703/200000000000000000000000000000 : ℝ)*base71 + (685489589262703/100000000000000000000000000000 : ℝ)*base73 + (1293347696762703/200000000000000000000000000000 : ℝ)*base75 + (478349683562703/200000000000000000000000000000 : ℝ)*base77 + (935189112162703/200000000000000000000000000000 : ℝ)*base79 + (51252706362703/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4229607/500000000000000000000 : ℝ)*base90 + (4229607/500000000000000000000 : ℝ)*base92 + (4229607/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1317_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (49/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6763/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1317_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1317_s1_0 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2012445933/10000000000 : ℝ)*x 0 + (2826766469/5000000000 : ℝ)*x 1 + (251925607/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2012445933/10000000000 : ℝ)^4277 ≤ (12149156027619/100000000000000 : ℝ)^3253 := by
    have hnat : (2012445933 : ℕ)^4277*100000000000000^3253 ≤ 12149156027619^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012445933 10000000000 12149156027619 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2826766469/5000000000 : ℝ)^4277 ≤ (47244757075607/100000000000000 : ℝ)^3253 := by
    have hnat : (2826766469 : ℕ)^4277*100000000000000^3253 ≤ 47244757075607^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2826766469 5000000000 47244757075607 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251925607/500000000 : ℝ)^4277 ≤ (8121217376713/20000000000000 : ℝ)^3253 := by
    have hnat : (251925607 : ℕ)^4277*20000000000000^3253 ≤ 8121217376713^3253*500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251925607 500000000 8121217376713 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2012445933/10000000000 : ℝ), (2826766469/5000000000 : ℝ), (251925607/500000000 : ℝ)] ![(12149156027619/100000000000000 : ℝ), (47244757075607/100000000000000 : ℝ), (8121217376713/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2012445933/10000000000 : ℝ)|^4277 ≤ (12149156027619/100000000000000 : ℝ)^3253
        have hw : |(-2012445933/10000000000 : ℝ)|=(2012445933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2826766469/5000000000 : ℝ)|^4277 ≤ (47244757075607/100000000000000 : ℝ)^3253
        have hw : |(2826766469/5000000000 : ℝ)|=(2826766469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251925607/500000000 : ℝ)|^4277 ≤ (8121217376713/20000000000000 : ℝ)^3253
        have hw : |(251925607/500000000 : ℝ)|=(251925607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s1_1 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2704169367/5000000000 : ℝ)*x 0 + (-234134871/1000000000 : ℝ)*x 1 + (5038512317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704169367/5000000000 : ℝ)^4277 ≤ (44569323139983/100000000000000 : ℝ)^3253 := by
    have hnat : (2704169367 : ℕ)^4277*100000000000000^3253 ≤ 44569323139983^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704169367 5000000000 44569323139983 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234134871/1000000000 : ℝ)^4277 ≤ (463268377641/3125000000000 : ℝ)^3253 := by
    have hnat : (234134871 : ℕ)^4277*3125000000000^3253 ≤ 463268377641^3253*1000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234134871 1000000000 463268377641 3125000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5038512317/10000000000 : ℝ)^4277 ≤ (20303044379533/50000000000000 : ℝ)^3253 := by
    have hnat : (5038512317 : ℕ)^4277*50000000000000^3253 ≤ 20303044379533^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5038512317 10000000000 20303044379533 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704169367/5000000000 : ℝ), (-234134871/1000000000 : ℝ), (5038512317/10000000000 : ℝ)] ![(44569323139983/100000000000000 : ℝ), (463268377641/3125000000000 : ℝ), (20303044379533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704169367/5000000000 : ℝ)|^4277 ≤ (44569323139983/100000000000000 : ℝ)^3253
        have hw : |(2704169367/5000000000 : ℝ)|=(2704169367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-234134871/1000000000 : ℝ)|^4277 ≤ (463268377641/3125000000000 : ℝ)^3253
        have hw : |(-234134871/1000000000 : ℝ)|=(234134871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5038512317/10000000000 : ℝ)|^4277 ≤ (20303044379533/50000000000000 : ℝ)^3253
        have hw : |(5038512317/10000000000 : ℝ)|=(5038512317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s1_2 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5408338601/10000000000 : ℝ)*x 0 + (1259627997/2500000000 : ℝ)*x 1 + (-2341349303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5408338601/10000000000 : ℝ)^4277 ≤ (22284660849467/50000000000000 : ℝ)^3253 := by
    have hnat : (5408338601 : ℕ)^4277*50000000000000^3253 ≤ 22284660849467^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408338601 10000000000 22284660849467 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1259627997/2500000000 : ℝ)^4277 ≤ (8121217054593/20000000000000 : ℝ)^3253 := by
    have hnat : (1259627997 : ℕ)^4277*20000000000000^3253 ≤ 8121217054593^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259627997 2500000000 8121217054593 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2341349303/10000000000 : ℝ)^4277 ≤ (2964918604219/20000000000000 : ℝ)^3253 := by
    have hnat : (2341349303 : ℕ)^4277*20000000000000^3253 ≤ 2964918604219^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341349303 10000000000 2964918604219 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5408338601/10000000000 : ℝ), (1259627997/2500000000 : ℝ), (-2341349303/10000000000 : ℝ)] ![(22284660849467/50000000000000 : ℝ), (8121217054593/20000000000000 : ℝ), (2964918604219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5408338601/10000000000 : ℝ)|^4277 ≤ (22284660849467/50000000000000 : ℝ)^3253
        have hw : |(5408338601/10000000000 : ℝ)|=(5408338601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1259627997/2500000000 : ℝ)|^4277 ≤ (8121217054593/20000000000000 : ℝ)^3253
        have hw : |(1259627997/2500000000 : ℝ)|=(1259627997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2341349303/10000000000 : ℝ)|^4277 ≤ (2964918604219/20000000000000 : ℝ)^3253
        have hw : |(-2341349303/10000000000 : ℝ)|=(2341349303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s1_3 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148371863/5000000000 : ℝ)*x 0 + (3703081929/10000000000 : ℝ)*x 1 + (49791797/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148371863/5000000000 : ℝ)^4277 ≤ (32934931012869/100000000000000 : ℝ)^3253 := by
    have hnat : (2148371863 : ℕ)^4277*100000000000000^3253 ≤ 32934931012869^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148371863 5000000000 32934931012869 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3703081929/10000000000 : ℝ)^4277 ≤ (27086503226349/100000000000000 : ℝ)^3253 := by
    have hnat : (3703081929 : ℕ)^4277*100000000000000^3253 ≤ 27086503226349^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3703081929 10000000000 27086503226349 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49791797/100000000 : ℝ)^4277 ≤ (39978565736969/100000000000000 : ℝ)^3253 := by
    have hnat : (49791797 : ℕ)^4277*100000000000000^3253 ≤ 39978565736969^3253*100000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49791797 100000000 39978565736969 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148371863/5000000000 : ℝ), (3703081929/10000000000 : ℝ), (49791797/100000000 : ℝ)] ![(32934931012869/100000000000000 : ℝ), (27086503226349/100000000000000 : ℝ), (39978565736969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148371863/5000000000 : ℝ)|^4277 ≤ (32934931012869/100000000000000 : ℝ)^3253
        have hw : |(2148371863/5000000000 : ℝ)|=(2148371863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3703081929/10000000000 : ℝ)|^4277 ≤ (27086503226349/100000000000000 : ℝ)^3253
        have hw : |(3703081929/10000000000 : ℝ)|=(3703081929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49791797/100000000 : ℝ)|^4277 ≤ (39978565736969/100000000000000 : ℝ)^3253
        have hw : |(49791797/100000000 : ℝ)|=(49791797/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s1_4 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2013030773/10000000000 : ℝ)*x 0 + (5046378493/10000000000 : ℝ)*x 1 + (2822760247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013030773/10000000000 : ℝ)^4277 ≤ (2430759667243/20000000000000 : ℝ)^3253 := by
    have hnat : (2013030773 : ℕ)^4277*20000000000000^3253 ≤ 2430759667243^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013030773 10000000000 2430759667243 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5046378493/10000000000 : ℝ)^4277 ≤ (20344729815787/50000000000000 : ℝ)^3253 := by
    have hnat : (5046378493 : ℕ)^4277*50000000000000^3253 ≤ 20344729815787^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5046378493 10000000000 20344729815787 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2822760247/5000000000 : ℝ)^4277 ≤ (23578371009797/50000000000000 : ℝ)^3253 := by
    have hnat : (2822760247 : ℕ)^4277*50000000000000^3253 ≤ 23578371009797^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2822760247 5000000000 23578371009797 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2013030773/10000000000 : ℝ), (5046378493/10000000000 : ℝ), (2822760247/5000000000 : ℝ)] ![(2430759667243/20000000000000 : ℝ), (20344729815787/50000000000000 : ℝ), (23578371009797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2013030773/10000000000 : ℝ)|^4277 ≤ (2430759667243/20000000000000 : ℝ)^3253
        have hw : |(-2013030773/10000000000 : ℝ)|=(2013030773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5046378493/10000000000 : ℝ)|^4277 ≤ (20344729815787/50000000000000 : ℝ)^3253
        have hw : |(5046378493/10000000000 : ℝ)|=(5046378493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2822760247/5000000000 : ℝ)|^4277 ≤ (23578371009797/50000000000000 : ℝ)^3253
        have hw : |(2822760247/5000000000 : ℝ)|=(2822760247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s1_5 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2624544379/5000000000 : ℝ)*x 0 + (-1734340883/10000000000 : ℝ)*x 1 + (1411380039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624544379/5000000000 : ℝ)^4277 ≤ (42851907014623/100000000000000 : ℝ)^3253 := by
    have hnat : (2624544379 : ℕ)^4277*100000000000000^3253 ≤ 42851907014623^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624544379 5000000000 42851907014623 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1734340883/10000000000 : ℝ)^4277 ≤ (1998270931861/20000000000000 : ℝ)^3253 := by
    have hnat : (1734340883 : ℕ)^4277*20000000000000^3253 ≤ 1998270931861^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1734340883 10000000000 1998270931861 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1411380039/2500000000 : ℝ)^4277 ≤ (23578369153781/50000000000000 : ℝ)^3253 := by
    have hnat : (1411380039 : ℕ)^4277*50000000000000^3253 ≤ 23578369153781^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1411380039 2500000000 23578369153781 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624544379/5000000000 : ℝ), (-1734340883/10000000000 : ℝ), (1411380039/2500000000 : ℝ)] ![(42851907014623/100000000000000 : ℝ), (1998270931861/20000000000000 : ℝ), (23578369153781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624544379/5000000000 : ℝ)|^4277 ≤ (42851907014623/100000000000000 : ℝ)^3253
        have hw : |(2624544379/5000000000 : ℝ)|=(2624544379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1734340883/10000000000 : ℝ)|^4277 ≤ (1998270931861/20000000000000 : ℝ)^3253
        have hw : |(-1734340883/10000000000 : ℝ)|=(1734340883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1411380039/2500000000 : ℝ)|^4277 ≤ (23578369153781/50000000000000 : ℝ)^3253
        have hw : |(1411380039/2500000000 : ℝ)|=(1411380039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s1_6 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2624544313/5000000000 : ℝ)*x 0 + (70569/125000 : ℝ)*x 1 + (-108396331/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624544313/5000000000 : ℝ)^4277 ≤ (214259527989/500000000000 : ℝ)^3253 := by
    have hnat : (2624544313 : ℕ)^4277*500000000000^3253 ≤ 214259527989^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624544313 5000000000 214259527989 500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70569/125000 : ℝ)^4277 ≤ (11789184148579/25000000000000 : ℝ)^3253 := by
    have hnat : (70569 : ℕ)^4277*25000000000000^3253 ≤ 11789184148579^3253*125000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70569 125000 11789184148579 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108396331/625000000 : ℝ)^4277 ≤ (999135778751/10000000000000 : ℝ)^3253 := by
    have hnat : (108396331 : ℕ)^4277*10000000000000^3253 ≤ 999135778751^3253*625000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108396331 625000000 999135778751 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624544313/5000000000 : ℝ), (70569/125000 : ℝ), (-108396331/625000000 : ℝ)] ![(214259527989/500000000000 : ℝ), (11789184148579/25000000000000 : ℝ), (999135778751/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624544313/5000000000 : ℝ)|^4277 ≤ (214259527989/500000000000 : ℝ)^3253
        have hw : |(2624544313/5000000000 : ℝ)|=(2624544313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70569/125000 : ℝ)|^4277 ≤ (11789184148579/25000000000000 : ℝ)^3253
        have hw : |(70569/125000 : ℝ)|=(70569/125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108396331/625000000 : ℝ)|^4277 ≤ (999135778751/10000000000000 : ℝ)^3253
        have hw : |(-108396331/625000000 : ℝ)|=(108396331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s1_7 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074489121/2500000000 : ℝ)*x 0 + (1240714401/2500000000 : ℝ)*x 1 + (185985331/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074489121/2500000000 : ℝ)^4277 ≤ (32947153678559/100000000000000 : ℝ)^3253 := by
    have hnat : (1074489121 : ℕ)^4277*100000000000000^3253 ≤ 32947153678559^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074489121 2500000000 32947153678559 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1240714401/2500000000 : ℝ)^4277 ≤ (39806348655289/100000000000000 : ℝ)^3253 := by
    have hnat : (1240714401 : ℕ)^4277*100000000000000^3253 ≤ 39806348655289^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240714401 2500000000 39806348655289 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185985331/500000000 : ℝ)^4277 ≤ (27246497648767/100000000000000 : ℝ)^3253 := by
    have hnat : (185985331 : ℕ)^4277*100000000000000^3253 ≤ 27246497648767^3253*500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185985331 500000000 27246497648767 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074489121/2500000000 : ℝ), (1240714401/2500000000 : ℝ), (185985331/500000000 : ℝ)] ![(32947153678559/100000000000000 : ℝ), (39806348655289/100000000000000 : ℝ), (27246497648767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074489121/2500000000 : ℝ)|^4277 ≤ (32947153678559/100000000000000 : ℝ)^3253
        have hw : |(1074489121/2500000000 : ℝ)|=(1074489121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1240714401/2500000000 : ℝ)|^4277 ≤ (39806348655289/100000000000000 : ℝ)^3253
        have hw : |(1240714401/2500000000 : ℝ)|=(1240714401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(185985331/500000000 : ℝ)|^4277 ≤ (27246497648767/100000000000000 : ℝ)^3253
        have hw : |(185985331/500000000 : ℝ)|=(185985331/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1317_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6763/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (49/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (6653/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4913/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6763/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (49/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6763/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (49/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6763/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (49/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6763/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (49/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6763/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (49/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6763/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (49/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (49/4000 : ℝ) ^ (1069/256 : ℝ) ≤ (259665669581/25000000000000000000 : ℝ) := by
    have hpowers : (49/4000 : ℝ)^1069 ≤ (259665669581/25000000000000000000 : ℝ)^256 := by
      have hnat : (49 : ℕ)^1069*25000000000000000000^256 ≤ 259665669581^256*4000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        49 4000 259665669581 25000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (49/4000 : ℝ)) (X := (259665669581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hpowhi : (6763/25000 : ℝ) ^ (1069/256 : ℝ) ≤ (106396862338924001/25000000000000000000 : ℝ) := by
    have hpowers : (6763/25000 : ℝ)^1069 ≤ (106396862338924001/25000000000000000000 : ℝ)^256 := by
      have hnat : (6763 : ℕ)^1069*25000000000000000000^256 ≤ 106396862338924001^256*25000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6763 25000 106396862338924001 25000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6763/25000 : ℝ)) (X := (106396862338924001/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000259665669581/12500000000000000000 : ℝ) ≤ (10000000049746987/10000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (12500000259665669581/12500000000000000000 : ℝ)^256 ≤ (10000000049746987/10000000000000000 : ℝ)^1069 := by
      have hnat : (12500000259665669581 : ℕ)^256*10000000000000000^1069 ≤ 10000000049746987^1069*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000259665669581 12500000000000000000 10000000049746987 10000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000049746987/10000000000000000 : ℝ)) (X := (12500000259665669581/12500000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12553198561002296791/12500000000000000000 : ℝ) ≤ (2002035075240639/2000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (12553198561002296791/12500000000000000000 : ℝ)^256 ≤ (2002035075240639/2000000000000000 : ℝ)^1069 := by
      have hnat : (12553198561002296791 : ℕ)^256*2000000000000000^1069 ≤ 2002035075240639^1069*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12553198561002296791 12500000000000000000 2002035075240639 2000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002035075240639/2000000000000000 : ℝ)) (X := (12553198561002296791/12500000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12606396862338924001/12500000000000000000 : ℝ) ≤ (10020350702659403/10000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (12606396862338924001/12500000000000000000 : ℝ)^256 ≤ (10020350702659403/10000000000000000 : ℝ)^1069 := by
      have hnat : (12606396862338924001 : ℕ)^256*10000000000000000^1069 ≤ 10020350702659403^1069*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12606396862338924001 12500000000000000000 10020350702659403 10000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020350702659403/10000000000000000 : ℝ)) (X := (12606396862338924001/12500000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(259665669581/25000000000000000000 : ℝ) ≤ ((258245071734997723649/258270000000000000000 : ℝ)+2*(635957903513/161418750000000 : ℝ)*(49/4000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (258245071734997723649/258270000000000000000 : ℝ)+2*(635957903513/161418750000000 : ℝ)*(49/4000 : ℝ)=(10000000049746987/10000000000000000 : ℝ) by norm_num, show 1+2*(259665669581/25000000000000000000 : ℝ)=(12500000259665669581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(106396862338924001/25000000000000000000 : ℝ)+(259665669581/25000000000000000000 : ℝ) ≤ ((258245071734997723649/258270000000000000000 : ℝ)+(635957903513/161418750000000 : ℝ)*((6763/25000 : ℝ)+(49/4000 : ℝ)))^(1069/256 : ℝ) := by
    rw [show (258245071734997723649/258270000000000000000 : ℝ)+(635957903513/161418750000000 : ℝ)*((6763/25000 : ℝ)+(49/4000 : ℝ))=(2002035075240639/2000000000000000 : ℝ) by norm_num, show 1+(106396862338924001/25000000000000000000 : ℝ)+(259665669581/25000000000000000000 : ℝ)=(12553198561002296791/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(106396862338924001/25000000000000000000 : ℝ) ≤ ((258245071734997723649/258270000000000000000 : ℝ)+2*(635957903513/161418750000000 : ℝ)*(6763/25000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (258245071734997723649/258270000000000000000 : ℝ)+2*(635957903513/161418750000000 : ℝ)*(6763/25000 : ℝ)=(10020350702659403/10000000000000000 : ℝ) by norm_num, show 1+2*(106396862338924001/25000000000000000000 : ℝ)=(12606396862338924001/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (258245071734997723649/258270000000000000000 : ℝ)*(X 1 0+X 2 0)+(635957903513/161418750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (49/4000 : ℝ)) (hi := (6763/25000 : ℝ)) (c := (258245071734997723649/258270000000000000000 : ℝ)) (alpha := (635957903513/161418750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (258245071734997723649/258270000000000000000 : ℝ)*(X 0 1+X 2 1)+(635957903513/161418750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (49/4000 : ℝ)) (hi := (6763/25000 : ℝ)) (c := (258245071734997723649/258270000000000000000 : ℝ)) (alpha := (635957903513/161418750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (258245071734997723649/258270000000000000000 : ℝ)*(X 0 2+X 1 2)+(635957903513/161418750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (49/4000 : ℝ)) (hi := (6763/25000 : ℝ)) (c := (258245071734997723649/258270000000000000000 : ℝ)) (alpha := (635957903513/161418750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2012445933/10000000000 : ℝ)*X 0 0+(2826766469/5000000000 : ℝ)*X 0 1+(251925607/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2704169367/5000000000 : ℝ)*X 1 0+(-234134871/1000000000 : ℝ)*X 1 1+(5038512317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5408338601/10000000000 : ℝ)*X 2 0+(1259627997/2500000000 : ℝ)*X 2 1+(-2341349303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2148371863/5000000000 : ℝ)*X 0 0+(3703081929/10000000000 : ℝ)*X 0 1+(49791797/100000000 : ℝ)*X 0 2+(2148371863/5000000000 : ℝ)*X 1 0+(3703081929/10000000000 : ℝ)*X 1 1+(49791797/100000000 : ℝ)*X 1 2+(2148371863/5000000000 : ℝ)*X 2 0+(3703081929/10000000000 : ℝ)*X 2 1+(49791797/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2013030773/10000000000 : ℝ)*X 0 0+(5046378493/10000000000 : ℝ)*X 0 1+(2822760247/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2624544379/5000000000 : ℝ)*X 1 0+(-1734340883/10000000000 : ℝ)*X 1 1+(1411380039/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2624544313/5000000000 : ℝ)*X 2 0+(70569/125000 : ℝ)*X 2 1+(-108396331/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1074489121/2500000000 : ℝ)*X 0 0+(1240714401/2500000000 : ℝ)*X 0 1+(185985331/500000000 : ℝ)*X 0 2+(1074489121/2500000000 : ℝ)*X 1 0+(1240714401/2500000000 : ℝ)*X 1 1+(185985331/500000000 : ℝ)*X 1 2+(1074489121/2500000000 : ℝ)*X 2 0+(1240714401/2500000000 : ℝ)*X 2 1+(185985331/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21484079330221801457413753971/2152250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122788769/100000000000000 : ℝ)*(base1) + (1675669741/100000000000000 : ℝ)*(base19) + (327136849/20000000000000 : ℝ)*(base23) + (153743233/50000000000000 : ℝ)*(upper3) + (15486811/25000000000000 : ℝ)*(upper5) + (1204813816590621/100000000000000 : ℝ)*(major0) + (1204813816590621/100000000000000 : ℝ)*(major1) + (1204813816590621/100000000000000 : ℝ)*(major2) + (50811623453467/3125000000000 : ℝ)*(sp0) + (1625978237733357/100000000000000 : ℝ)*(sp1) + (812989138859427/50000000000000 : ℝ)*(sp2) + (195910632701249/25000000000000 : ℝ)*(sp3) + (8085680923/100000000000000 : ℝ)*(sp4) + (4733446087/100000000000000 : ℝ)*(sp7) + (195911846759963/25000000000000 : ℝ)*(f.failure) + (812989956701549/50000000000000 : ℝ)*(f.sum) + (90139344382271/43045000000000000000000000000 : ℝ)*base65 + (63330943081326365343/8609000000000000000000000000000000 : ℝ)*base67 + (1451190796655365343/8609000000000000000000000000000000 : ℝ)*base69 + (54677969178835365343/8609000000000000000000000000000000 : ℝ)*base71 + (58609597703883/21522500000000000000000000000 : ℝ)*base73 + (52088794634032365343/8609000000000000000000000000000000 : ℝ)*base75 + (43600482922291365343/8609000000000000000000000000000000 : ℝ)*base77 + (24924730424442634657/8609000000000000000000000000000000 : ℝ)*base80 + (5082474952977/21522500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (237103/125000000000000000000 : ℝ)*base90 + (237103/125000000000000000000 : ℝ)*base92 + (237103/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7107901101407636224116636171/2152250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (500970289/100000000000000 : ℝ)*(base19) + (114906861/25000000000000 : ℝ)*(base23) + (25015187/100000000000000 : ℝ)*(upper2) + (7269321/25000000000000 : ℝ)*(upper3) + (56535739/50000000000000 : ℝ)*(upper5) + (1236730537952821/100000000000000 : ℝ)*(major0) + (1236730537952821/100000000000000 : ℝ)*(major1) + (1236730537952821/100000000000000 : ℝ)*(major2) + (2185395077/100000000000000 : ℝ)*(sp1) + (317661093/50000000000000 : ℝ)*(sp2) + (834526988398021/50000000000000 : ℝ)*(sp4) + (1669051290430677/100000000000000 : ℝ)*(sp5) + (417263220461603/25000000000000 : ℝ)*(sp6) + (804406989024783/100000000000000 : ℝ)*(sp7) + (804406989024783/100000000000000 : ℝ)*(f.failure) + (834526988398021/50000000000000 : ℝ)*(f.sum) + (109345958025229/64567500000000000000000000000 : ℝ)*base65 + (84712520266208763829/25827000000000000000000000000000000 : ℝ)*base67 + (26614075023818763829/25827000000000000000000000000000000 : ℝ)*base69 + (10344706381322763829/25827000000000000000000000000000000 : ℝ)*base71 + (70866069444817/129135000000000000000000000000 : ℝ)*base74 + (85237606934952236171/25827000000000000000000000000000000 : ℝ)*base76 + (215086440629744763829/25827000000000000000000000000000000 : ℝ)*base77 + (113605674277934763829/25827000000000000000000000000000000 : ℝ)*base79 + (6594973201241/64567500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1651523/500000000000000000000 : ℝ)*base90 + (1651523/500000000000000000000 : ℝ)*base92 + (1651523/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1317_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6763/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (49/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6653/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4913/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1317_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1317_s2_0 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-205482593/1000000000 : ℝ)*x 0 + (109735751/200000000 : ℝ)*x 1 + (5178149133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205482593/1000000000 : ℝ)^4277 ≤ (1560831467543/12500000000000 : ℝ)^3253 := by
    have hnat : (205482593 : ℕ)^4277*12500000000000^3253 ≤ 1560831467543^3253*1000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205482593 1000000000 1560831467543 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109735751/200000000 : ℝ)^4277 ≤ (22710623563841/50000000000000 : ℝ)^3253 := by
    have hnat : (109735751 : ℕ)^4277*50000000000000^3253 ≤ 22710623563841^3253*200000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109735751 200000000 22710623563841 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178149133/10000000000 : ℝ)^4277 ≤ (10523025279023/25000000000000 : ℝ)^3253 := by
    have hnat : (5178149133 : ℕ)^4277*25000000000000^3253 ≤ 10523025279023^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178149133 10000000000 10523025279023 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205482593/1000000000 : ℝ), (109735751/200000000 : ℝ), (5178149133/10000000000 : ℝ)] ![(1560831467543/12500000000000 : ℝ), (22710623563841/50000000000000 : ℝ), (10523025279023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205482593/1000000000 : ℝ)|^4277 ≤ (1560831467543/12500000000000 : ℝ)^3253
        have hw : |(-205482593/1000000000 : ℝ)|=(205482593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109735751/200000000 : ℝ)|^4277 ≤ (22710623563841/50000000000000 : ℝ)^3253
        have hw : |(109735751/200000000 : ℝ)|=(109735751/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178149133/10000000000 : ℝ)|^4277 ≤ (10523025279023/25000000000000 : ℝ)^3253
        have hw : |(5178149133/10000000000 : ℝ)|=(5178149133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s2_1 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367739303/10000000000 : ℝ)*x 0 + (-1107264147/5000000000 : ℝ)*x 1 + (323634293/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367739303/10000000000 : ℝ)^4277 ≤ (22064975268781/50000000000000 : ℝ)^3253 := by
    have hnat : (5367739303 : ℕ)^4277*50000000000000^3253 ≤ 22064975268781^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367739303 10000000000 22064975268781 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107264147/5000000000 : ℝ)^4277 ≤ (13777953095317/100000000000000 : ℝ)^3253 := by
    have hnat : (1107264147 : ℕ)^4277*100000000000000^3253 ≤ 13777953095317^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107264147 5000000000 13777953095317 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323634293/625000000 : ℝ)^4277 ≤ (42092096360099/100000000000000 : ℝ)^3253 := by
    have hnat : (323634293 : ℕ)^4277*100000000000000^3253 ≤ 42092096360099^3253*625000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323634293 625000000 42092096360099 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367739303/10000000000 : ℝ), (-1107264147/5000000000 : ℝ), (323634293/625000000 : ℝ)] ![(22064975268781/50000000000000 : ℝ), (13777953095317/100000000000000 : ℝ), (42092096360099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367739303/10000000000 : ℝ)|^4277 ≤ (22064975268781/50000000000000 : ℝ)^3253
        have hw : |(5367739303/10000000000 : ℝ)|=(5367739303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1107264147/5000000000 : ℝ)|^4277 ≤ (13777953095317/100000000000000 : ℝ)^3253
        have hw : |(-1107264147/5000000000 : ℝ)|=(1107264147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323634293/625000000 : ℝ)|^4277 ≤ (42092096360099/100000000000000 : ℝ)^3253
        have hw : |(323634293/625000000 : ℝ)|=(323634293/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s2_2 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367738659/10000000000 : ℝ)*x 0 + (1035629863/2000000000 : ℝ)*x 1 + (-88581133/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367738659/10000000000 : ℝ)^4277 ≤ (22064971788189/50000000000000 : ℝ)^3253 := by
    have hnat : (5367738659 : ℕ)^4277*50000000000000^3253 ≤ 22064971788189^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367738659 10000000000 22064971788189 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035629863/2000000000 : ℝ)^4277 ≤ (1052302576531/2500000000000 : ℝ)^3253 := by
    have hnat : (1035629863 : ℕ)^4277*2500000000000^3253 ≤ 1052302576531^3253*2000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035629863 2000000000 1052302576531 2500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88581133/400000000 : ℝ)^4277 ≤ (13777953348901/100000000000000 : ℝ)^3253 := by
    have hnat : (88581133 : ℕ)^4277*100000000000000^3253 ≤ 13777953348901^3253*400000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88581133 400000000 13777953348901 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367738659/10000000000 : ℝ), (1035629863/2000000000 : ℝ), (-88581133/400000000 : ℝ)] ![(22064971788189/50000000000000 : ℝ), (1052302576531/2500000000000 : ℝ), (13777953348901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367738659/10000000000 : ℝ)|^4277 ≤ (22064971788189/50000000000000 : ℝ)^3253
        have hw : |(5367738659/10000000000 : ℝ)|=(5367738659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035629863/2000000000 : ℝ)|^4277 ≤ (1052302576531/2500000000000 : ℝ)^3253
        have hw : |(1035629863/2000000000 : ℝ)|=(1035629863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88581133/400000000 : ℝ)|^4277 ≤ (13777953348901/100000000000000 : ℝ)^3253
        have hw : |(-88581133/400000000 : ℝ)|=(88581133/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s2_3 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540786583/1250000000 : ℝ)*x 0 + (4017258201/10000000000 : ℝ)*x 1 + (1164414123/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540786583/1250000000 : ℝ)^4277 ≤ (6646609152189/20000000000000 : ℝ)^3253 := by
    have hnat : (540786583 : ℕ)^4277*20000000000000^3253 ≤ 6646609152189^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540786583 1250000000 6646609152189 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4017258201/10000000000 : ℝ)^4277 ≤ (30147564708273/100000000000000 : ℝ)^3253 := by
    have hnat : (4017258201 : ℕ)^4277*100000000000000^3253 ≤ 30147564708273^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017258201 10000000000 30147564708273 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1164414123/2500000000 : ℝ)^4277 ≤ (36619389510213/100000000000000 : ℝ)^3253 := by
    have hnat : (1164414123 : ℕ)^4277*100000000000000^3253 ≤ 36619389510213^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164414123 2500000000 36619389510213 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540786583/1250000000 : ℝ), (4017258201/10000000000 : ℝ), (1164414123/2500000000 : ℝ)] ![(6646609152189/20000000000000 : ℝ), (30147564708273/100000000000000 : ℝ), (36619389510213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540786583/1250000000 : ℝ)|^4277 ≤ (6646609152189/20000000000000 : ℝ)^3253
        have hw : |(540786583/1250000000 : ℝ)|=(540786583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4017258201/10000000000 : ℝ)|^4277 ≤ (30147564708273/100000000000000 : ℝ)^3253
        have hw : |(4017258201/10000000000 : ℝ)|=(4017258201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1164414123/2500000000 : ℝ)|^4277 ≤ (36619389510213/100000000000000 : ℝ)^3253
        have hw : |(1164414123/2500000000 : ℝ)|=(1164414123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s2_4 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-513724851/2500000000 : ℝ)*x 0 + (5180139399/10000000000 : ℝ)*x 1 + (5484779059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513724851/2500000000 : ℝ)^4277 ≤ (12487238773021/100000000000000 : ℝ)^3253 := by
    have hnat : (513724851 : ℕ)^4277*100000000000000^3253 ≤ 12487238773021^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513724851 2500000000 12487238773021 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180139399/10000000000 : ℝ)^4277 ≤ (842267472419/2000000000000 : ℝ)^3253 := by
    have hnat : (5180139399 : ℕ)^4277*2000000000000^3253 ≤ 842267472419^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180139399 10000000000 842267472419 2000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484779059/10000000000 : ℝ)^4277 ≤ (45399387590529/100000000000000 : ℝ)^3253 := by
    have hnat : (5484779059 : ℕ)^4277*100000000000000^3253 ≤ 45399387590529^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484779059 10000000000 45399387590529 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-513724851/2500000000 : ℝ), (5180139399/10000000000 : ℝ), (5484779059/10000000000 : ℝ)] ![(12487238773021/100000000000000 : ℝ), (842267472419/2000000000000 : ℝ), (45399387590529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-513724851/2500000000 : ℝ)|^4277 ≤ (12487238773021/100000000000000 : ℝ)^3253
        have hw : |(-513724851/2500000000 : ℝ)|=(513724851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180139399/10000000000 : ℝ)|^4277 ≤ (842267472419/2000000000000 : ℝ)^3253
        have hw : |(5180139399/10000000000 : ℝ)|=(5180139399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484779059/10000000000 : ℝ)|^4277 ≤ (45399387590529/100000000000000 : ℝ)^3253
        have hw : |(5484779059/10000000000 : ℝ)|=(5484779059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s2_5 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288407237/10000000000 : ℝ)*x 0 + (-953948727/5000000000 : ℝ)*x 1 + (5484779133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288407237/10000000000 : ℝ)^4277 ≤ (43274428672497/100000000000000 : ℝ)^3253 := by
    have hnat : (5288407237 : ℕ)^4277*100000000000000^3253 ≤ 43274428672497^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288407237 10000000000 43274428672497 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (953948727/5000000000 : ℝ)^4277 ≤ (11326182914681/100000000000000 : ℝ)^3253 := by
    have hnat : (953948727 : ℕ)^4277*100000000000000^3253 ≤ 11326182914681^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953948727 5000000000 11326182914681 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484779133/10000000000 : ℝ)^4277 ≤ (22699694197933/50000000000000 : ℝ)^3253 := by
    have hnat : (5484779133 : ℕ)^4277*50000000000000^3253 ≤ 22699694197933^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484779133 10000000000 22699694197933 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288407237/10000000000 : ℝ), (-953948727/5000000000 : ℝ), (5484779133/10000000000 : ℝ)] ![(43274428672497/100000000000000 : ℝ), (11326182914681/100000000000000 : ℝ), (22699694197933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288407237/10000000000 : ℝ)|^4277 ≤ (43274428672497/100000000000000 : ℝ)^3253
        have hw : |(5288407237/10000000000 : ℝ)|=(5288407237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-953948727/5000000000 : ℝ)|^4277 ≤ (11326182914681/100000000000000 : ℝ)^3253
        have hw : |(-953948727/5000000000 : ℝ)|=(953948727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484779133/10000000000 : ℝ)|^4277 ≤ (22699694197933/50000000000000 : ℝ)^3253
        have hw : |(5484779133/10000000000 : ℝ)|=(5484779133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s2_6 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661050917/1250000000 : ℝ)*x 0 + (2742389533/5000000000 : ℝ)*x 1 + (-190789741/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661050917/1250000000 : ℝ)^4277 ≤ (43274429737613/100000000000000 : ℝ)^3253 := by
    have hnat : (661050917 : ℕ)^4277*100000000000000^3253 ≤ 43274429737613^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661050917 1250000000 43274429737613 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742389533/5000000000 : ℝ)^4277 ≤ (45399387666709/100000000000000 : ℝ)^3253 := by
    have hnat : (2742389533 : ℕ)^4277*100000000000000^3253 ≤ 45399387666709^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742389533 5000000000 45399387666709 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190789741/1000000000 : ℝ)^4277 ≤ (2831545642813/25000000000000 : ℝ)^3253 := by
    have hnat : (190789741 : ℕ)^4277*25000000000000^3253 ≤ 2831545642813^3253*1000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190789741 1000000000 2831545642813 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661050917/1250000000 : ℝ), (2742389533/5000000000 : ℝ), (-190789741/1000000000 : ℝ)] ![(43274429737613/100000000000000 : ℝ), (45399387666709/100000000000000 : ℝ), (2831545642813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661050917/1250000000 : ℝ)|^4277 ≤ (43274429737613/100000000000000 : ℝ)^3253
        have hw : |(661050917/1250000000 : ℝ)|=(661050917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742389533/5000000000 : ℝ)|^4277 ≤ (45399387666709/100000000000000 : ℝ)^3253
        have hw : |(2742389533/5000000000 : ℝ)|=(2742389533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-190789741/1000000000 : ℝ)|^4277 ≤ (2831545642813/25000000000000 : ℝ)^3253
        have hw : |(-190789741/1000000000 : ℝ)|=(190789741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s2_7 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (27040273/62500000 : ℝ)*x 0 + (1163381197/2500000000 : ℝ)*x 1 + (4021430963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27040273/62500000 : ℝ)^4277 ≤ (8308642747251/25000000000000 : ℝ)^3253 := by
    have hnat : (27040273 : ℕ)^4277*25000000000000^3253 ≤ 8308642747251^3253*62500000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27040273 62500000 8308642747251 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163381197/2500000000 : ℝ)^4277 ≤ (7315337125197/20000000000000 : ℝ)^3253 := by
    have hnat : (1163381197 : ℕ)^4277*20000000000000^3253 ≤ 7315337125197^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163381197 2500000000 7315337125197 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021430963/10000000000 : ℝ)^4277 ≤ (6037748674791/20000000000000 : ℝ)^3253 := by
    have hnat : (4021430963 : ℕ)^4277*20000000000000^3253 ≤ 6037748674791^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021430963 10000000000 6037748674791 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27040273/62500000 : ℝ), (1163381197/2500000000 : ℝ), (4021430963/10000000000 : ℝ)] ![(8308642747251/25000000000000 : ℝ), (7315337125197/20000000000000 : ℝ), (6037748674791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27040273/62500000 : ℝ)|^4277 ≤ (8308642747251/25000000000000 : ℝ)^3253
        have hw : |(27040273/62500000 : ℝ)|=(27040273/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1163381197/2500000000 : ℝ)|^4277 ≤ (7315337125197/20000000000000 : ℝ)^3253
        have hw : |(1163381197/2500000000 : ℝ)|=(1163381197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021430963/10000000000 : ℝ)|^4277 ≤ (6037748674791/20000000000000 : ℝ)^3253
        have hw : |(4021430963/10000000000 : ℝ)|=(4021430963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1317_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4913/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6653/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9683/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16207/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4913/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6653/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4913/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6653/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4913/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6653/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4913/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6653/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4913/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6653/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4913/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6653/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6653/100000 : ℝ) ^ (1069/256 : ℝ) ≤ (60834318493931/5000000000000000000 : ℝ) := by
    have hpowers : (6653/100000 : ℝ)^1069 ≤ (60834318493931/5000000000000000000 : ℝ)^256 := by
      have hnat : (6653 : ℕ)^1069*5000000000000000000^256 ≤ 60834318493931^256*100000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6653 100000 60834318493931 5000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6653/100000 : ℝ)) (X := (60834318493931/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hpowhi : (4913/25000 : ℝ) ^ (1069/256 : ℝ) ≤ (56026201955174353/50000000000000000000 : ℝ) := by
    have hpowers : (4913/25000 : ℝ)^1069 ≤ (56026201955174353/50000000000000000000 : ℝ)^256 := by
      have hnat : (4913 : ℕ)^1069*50000000000000000000^256 ≤ 56026201955174353^256*25000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4913 25000 56026201955174353 50000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4913/25000 : ℝ)) (X := (56026201955174353/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500060834318493931/2500000000000000000 : ℝ) ≤ (5000029136466663/5000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (2500060834318493931/2500000000000000000 : ℝ)^256 ≤ (5000029136466663/5000000000000000 : ℝ)^1069 := by
      have hnat : (2500060834318493931 : ℕ)^256*5000000000000000^1069 ≤ 5000029136466663^1069*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500060834318493931 2500000000000000000 5000029136466663 5000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000029136466663/5000000000000000 : ℝ)) (X := (2500060834318493931/2500000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50056634545140113663/50000000000000000000 : ℝ) ≤ (5001355678479439/5000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (50056634545140113663/50000000000000000000 : ℝ)^256 ≤ (5001355678479439/5000000000000000 : ℝ)^1069 := by
      have hnat : (50056634545140113663 : ℕ)^256*5000000000000000^1069 ≤ 5001355678479439^1069*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50056634545140113663 50000000000000000000 5001355678479439 5000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001355678479439/5000000000000000 : ℝ)) (X := (50056634545140113663/50000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25056026201955174353/25000000000000000000 : ℝ) ≤ (1000536444098443/1000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (25056026201955174353/25000000000000000000 : ℝ)^256 ≤ (1000536444098443/1000000000000000 : ℝ)^1069 := by
      have hnat : (25056026201955174353 : ℕ)^256*1000000000000000^1069 ≤ 1000536444098443^1069*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25056026201955174353 25000000000000000000 1000536444098443 1000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000536444098443/1000000000000000 : ℝ)) (X := (25056026201955174353/25000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(60834318493931/5000000000000000000 : ℝ) ≤ ((64977727776908154881/64995000000000000000 : ℝ)+2*(165817751597/81243750000000 : ℝ)*(6653/100000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (64977727776908154881/64995000000000000000 : ℝ)+2*(165817751597/81243750000000 : ℝ)*(6653/100000 : ℝ)=(5000029136466663/5000000000000000 : ℝ) by norm_num, show 1+2*(60834318493931/5000000000000000000 : ℝ)=(2500060834318493931/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(56026201955174353/50000000000000000000 : ℝ)+(60834318493931/5000000000000000000 : ℝ) ≤ ((64977727776908154881/64995000000000000000 : ℝ)+(165817751597/81243750000000 : ℝ)*((4913/25000 : ℝ)+(6653/100000 : ℝ)))^(1069/256 : ℝ) := by
    rw [show (64977727776908154881/64995000000000000000 : ℝ)+(165817751597/81243750000000 : ℝ)*((4913/25000 : ℝ)+(6653/100000 : ℝ))=(5001355678479439/5000000000000000 : ℝ) by norm_num, show 1+(56026201955174353/50000000000000000000 : ℝ)+(60834318493931/5000000000000000000 : ℝ)=(50056634545140113663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(56026201955174353/50000000000000000000 : ℝ) ≤ ((64977727776908154881/64995000000000000000 : ℝ)+2*(165817751597/81243750000000 : ℝ)*(4913/25000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (64977727776908154881/64995000000000000000 : ℝ)+2*(165817751597/81243750000000 : ℝ)*(4913/25000 : ℝ)=(1000536444098443/1000000000000000 : ℝ) by norm_num, show 1+2*(56026201955174353/50000000000000000000 : ℝ)=(25056026201955174353/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (64977727776908154881/64995000000000000000 : ℝ)*(X 1 0+X 2 0)+(165817751597/81243750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (6653/100000 : ℝ)) (hi := (4913/25000 : ℝ)) (c := (64977727776908154881/64995000000000000000 : ℝ)) (alpha := (165817751597/81243750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (64977727776908154881/64995000000000000000 : ℝ)*(X 0 1+X 2 1)+(165817751597/81243750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (6653/100000 : ℝ)) (hi := (4913/25000 : ℝ)) (c := (64977727776908154881/64995000000000000000 : ℝ)) (alpha := (165817751597/81243750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (64977727776908154881/64995000000000000000 : ℝ)*(X 0 2+X 1 2)+(165817751597/81243750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (6653/100000 : ℝ)) (hi := (4913/25000 : ℝ)) (c := (64977727776908154881/64995000000000000000 : ℝ)) (alpha := (165817751597/81243750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-205482593/1000000000 : ℝ)*X 0 0+(109735751/200000000 : ℝ)*X 0 1+(5178149133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5367739303/10000000000 : ℝ)*X 1 0+(-1107264147/5000000000 : ℝ)*X 1 1+(323634293/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5367738659/10000000000 : ℝ)*X 2 0+(1035629863/2000000000 : ℝ)*X 2 1+(-88581133/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540786583/1250000000 : ℝ)*X 0 0+(4017258201/10000000000 : ℝ)*X 0 1+(1164414123/2500000000 : ℝ)*X 0 2+(540786583/1250000000 : ℝ)*X 1 0+(4017258201/10000000000 : ℝ)*X 1 1+(1164414123/2500000000 : ℝ)*X 1 2+(540786583/1250000000 : ℝ)*X 2 0+(4017258201/10000000000 : ℝ)*X 2 1+(1164414123/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-513724851/2500000000 : ℝ)*X 0 0+(5180139399/10000000000 : ℝ)*X 0 1+(5484779059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288407237/10000000000 : ℝ)*X 1 0+(-953948727/5000000000 : ℝ)*X 1 1+(5484779133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661050917/1250000000 : ℝ)*X 2 0+(2742389533/5000000000 : ℝ)*X 2 1+(-190789741/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((27040273/62500000 : ℝ)*X 0 0+(1163381197/2500000000 : ℝ)*X 0 1+(4021430963/10000000000 : ℝ)*X 0 2+(27040273/62500000 : ℝ)*X 1 0+(1163381197/2500000000 : ℝ)*X 1 1+(4021430963/10000000000 : ℝ)*X 1 2+(27040273/62500000 : ℝ)*X 2 0+(1163381197/2500000000 : ℝ)*X 2 1+(4021430963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3054763957145399893819233/483593750000000000000000000000 : ℝ) := by norm_num
    linear_combination (2269596379/100000000000000 : ℝ)*(base19) + (10318693/781250000000 : ℝ)*(base23) + (60126629/20000000000000 : ℝ)*(lower2) + (359730561/50000000000000 : ℝ)*(upper3) + (153789891/100000000000000 : ℝ)*(upper5) + (7502536162583/312500000000 : ℝ)*(major0) + (7502536162583/312500000000 : ℝ)*(major1) + (7502536162583/312500000000 : ℝ)*(major2) + (810013717023779/25000000000000 : ℝ)*(sp0) + (1620030061467439/50000000000000 : ℝ)*(sp1) + (405007633967319/12500000000000 : ℝ)*(sp2) + (390385389269449/25000000000000 : ℝ)*(sp3) + (376221807/5000000000000 : ℝ)*(sp4) + (1898388413/10000000000000 : ℝ)*(sp7) + (780780270480963/50000000000000 : ℝ)*(f.failure) + (405007799066407/12500000000000 : ℝ)*(f.sum) + (1699443208013/232125000000000000000000000 : ℝ)*base65 + (2026752868322863/967187500000000000000000000000 : ℝ)*base67 + (3339321929266119/483593750000000000000000000000 : ℝ)*base69 + (910490961237747/241796875000000000000000000000 : ℝ)*base71 + (1053505999313/232125000000000000000000000 : ℝ)*base73 + (2617116554466119/483593750000000000000000000000 : ℝ)*base75 + (11804086495972863/967187500000000000000000000000 : ℝ)*base77 + (1891534039916613/967187500000000000000000000000 : ℝ)*base79 + (2657948880689/928500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2088103/250000000000000000000 : ℝ)*base90 + (2088103/250000000000000000000 : ℝ)*base92 + (2088103/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4686208899561706955550927883/541625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (846535883/50000000000000 : ℝ)*(base19) + (997312139/50000000000000 : ℝ)*(base23) + (46765251/20000000000000 : ℝ)*(upper3) + (46430609/50000000000000 : ℝ)*(lower4) + (129572793/100000000000000 : ℝ)*(upper5) + (1216152113242681/50000000000000 : ℝ)*(major0) + (1216152113242681/50000000000000 : ℝ)*(major1) + (1216152113242681/50000000000000 : ℝ)*(major2) + (18097485883/100000000000000 : ℝ)*(sp1) + (4479586543/20000000000000 : ℝ)*(sp2) + (164128192378697/5000000000000 : ℝ)*(sp4) + (3282544057016291/100000000000000 : ℝ)*(sp5) + (3282539455016947/100000000000000 : ℝ)*(sp6) + (791022158496253/50000000000000 : ℝ)*(sp7) + (791022158496253/50000000000000 : ℝ)*(f.failure) + (164128192378697/5000000000000 : ℝ)*(f.sum) + (21678017926339/4062187500000000000000000000 : ℝ)*base65 + (11392590841689908013/1083250000000000000000000000000000 : ℝ)*base68 + (14805245338777408013/1083250000000000000000000000000000 : ℝ)*base70 + (1312103365455908013/1083250000000000000000000000000000 : ℝ)*base72 + (37389571275029/16248750000000000000000000000 : ℝ)*base74 + (6363158255965158013/1083250000000000000000000000000000 : ℝ)*base76 + (8772873848634158013/1083250000000000000000000000000000 : ℝ)*base78 + (9241808438467658013/1083250000000000000000000000000000 : ℝ)*base80 + (246502332657011/64995000000000000000000000000 : ℝ)*base82 + (2490407/250000000000000000000 : ℝ)*base89 + (2490407/250000000000000000000 : ℝ)*base91 + (2490407/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1317_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4913/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6653/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9683/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16207/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1317_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1317_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9683/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16207/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1317_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1317_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1317_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9683/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16207/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1317_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
