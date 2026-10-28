-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1053_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:57:10.048996+00:00
-- url     : https://prove2.me/submissions/e59a623a-20c2-422e-96ef-da940e19e2e6

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
theorem support_rectangle_w1053_s6_0 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-442027111/2000000000 : ℝ)*x 0 + (5395182101/10000000000 : ℝ)*x 1 + (5263645171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442027111/2000000000 : ℝ)^4123 ≤ (13421337445911/100000000000000 : ℝ)^3099 := by
    have hnat : (442027111 : ℕ)^4123*100000000000000^3099 ≤ 13421337445911^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442027111 2000000000 13421337445911 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395182101/10000000000 : ℝ)^4123 ≤ (44000043743413/100000000000000 : ℝ)^3099 := by
    have hnat : (5395182101 : ℕ)^4123*100000000000000^3099 ≤ 44000043743413^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395182101 10000000000 44000043743413 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263645171/10000000000 : ℝ)^4123 ≤ (8515723760561/20000000000000 : ℝ)^3099 := by
    have hnat : (5263645171 : ℕ)^4123*20000000000000^3099 ≤ 8515723760561^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263645171 10000000000 8515723760561 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442027111/2000000000 : ℝ), (5395182101/10000000000 : ℝ), (5263645171/10000000000 : ℝ)] ![(13421337445911/100000000000000 : ℝ), (44000043743413/100000000000000 : ℝ), (8515723760561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442027111/2000000000 : ℝ)|^4123 ≤ (13421337445911/100000000000000 : ℝ)^3099
        have hw : |(-442027111/2000000000 : ℝ)|=(442027111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395182101/10000000000 : ℝ)|^4123 ≤ (44000043743413/100000000000000 : ℝ)^3099
        have hw : |(5395182101/10000000000 : ℝ)|=(5395182101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263645171/10000000000 : ℝ)|^4123 ≤ (8515723760561/20000000000000 : ℝ)^3099
        have hw : |(5263645171/10000000000 : ℝ)|=(5263645171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s6_1 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534515619/1000000000 : ℝ)*x 0 + (-2276885457/10000000000 : ℝ)*x 1 + (5263645171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534515619/1000000000 : ℝ)^4123 ≤ (43458084579071/100000000000000 : ℝ)^3099 := by
    have hnat : (534515619 : ℕ)^4123*100000000000000^3099 ≤ 43458084579071^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534515619 1000000000 43458084579071 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276885457/10000000000 : ℝ)^4123 ≤ (6981648302141/50000000000000 : ℝ)^3099 := by
    have hnat : (2276885457 : ℕ)^4123*50000000000000^3099 ≤ 6981648302141^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276885457 10000000000 6981648302141 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263645171/10000000000 : ℝ)^4123 ≤ (8515723760561/20000000000000 : ℝ)^3099 := by
    have hnat : (5263645171 : ℕ)^4123*20000000000000^3099 ≤ 8515723760561^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263645171 10000000000 8515723760561 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534515619/1000000000 : ℝ), (-2276885457/10000000000 : ℝ), (5263645171/10000000000 : ℝ)] ![(43458084579071/100000000000000 : ℝ), (6981648302141/50000000000000 : ℝ), (8515723760561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534515619/1000000000 : ℝ)|^4123 ≤ (43458084579071/100000000000000 : ℝ)^3099
        have hw : |(534515619/1000000000 : ℝ)|=(534515619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2276885457/10000000000 : ℝ)|^4123 ≤ (6981648302141/50000000000000 : ℝ)^3099
        have hw : |(-2276885457/10000000000 : ℝ)|=(2276885457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263645171/10000000000 : ℝ)|^4123 ≤ (8515723760561/20000000000000 : ℝ)^3099
        have hw : |(5263645171/10000000000 : ℝ)|=(5263645171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s6_2 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345156113/10000000000 : ℝ)*x 0 + (5263645221/10000000000 : ℝ)*x 1 + (-2276885493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345156113/10000000000 : ℝ)^4123 ≤ (43458083746171/100000000000000 : ℝ)^3099 := by
    have hnat : (5345156113 : ℕ)^4123*100000000000000^3099 ≤ 43458083746171^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345156113 10000000000 43458083746171 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263645221/10000000000 : ℝ)^4123 ≤ (4257861934091/10000000000000 : ℝ)^3099 := by
    have hnat : (5263645221 : ℕ)^4123*10000000000000^3099 ≤ 4257861934091^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263645221 10000000000 4257861934091 10000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276885493/10000000000 : ℝ)^4123 ≤ (13963296898007/100000000000000 : ℝ)^3099 := by
    have hnat : (2276885493 : ℕ)^4123*100000000000000^3099 ≤ 13963296898007^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276885493 10000000000 13963296898007 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345156113/10000000000 : ℝ), (5263645221/10000000000 : ℝ), (-2276885493/10000000000 : ℝ)] ![(43458083746171/100000000000000 : ℝ), (4257861934091/10000000000000 : ℝ), (13963296898007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345156113/10000000000 : ℝ)|^4123 ≤ (43458083746171/100000000000000 : ℝ)^3099
        have hw : |(5345156113/10000000000 : ℝ)|=(5345156113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263645221/10000000000 : ℝ)|^4123 ≤ (4257861934091/10000000000000 : ℝ)^3099
        have hw : |(5263645221/10000000000 : ℝ)|=(5263645221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2276885493/10000000000 : ℝ)|^4123 ≤ (13963296898007/100000000000000 : ℝ)^3099
        have hw : |(-2276885493/10000000000 : ℝ)|=(2276885493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s6_3 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4377335299/10000000000 : ℝ)*x 0 + (1062672347/2500000000 : ℝ)*x 1 + (1126954601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377335299/10000000000 : ℝ)^4123 ≤ (4164521263447/12500000000000 : ℝ)^3099 := by
    have hnat : (4377335299 : ℕ)^4123*12500000000000^3099 ≤ 4164521263447^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377335299 10000000000 4164521263447 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062672347/2500000000 : ℝ)^4123 ≤ (500623848861/1562500000000 : ℝ)^3099 := by
    have hnat : (1062672347 : ℕ)^4123*1562500000000^3099 ≤ 500623848861^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062672347 2500000000 500623848861 1562500000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126954601/2500000000 : ℝ)^4123 ≤ (17321951777551/50000000000000 : ℝ)^3099 := by
    have hnat : (1126954601 : ℕ)^4123*50000000000000^3099 ≤ 17321951777551^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126954601 2500000000 17321951777551 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377335299/10000000000 : ℝ), (1062672347/2500000000 : ℝ), (1126954601/2500000000 : ℝ)] ![(4164521263447/12500000000000 : ℝ), (500623848861/1562500000000 : ℝ), (17321951777551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377335299/10000000000 : ℝ)|^4123 ≤ (4164521263447/12500000000000 : ℝ)^3099
        have hw : |(4377335299/10000000000 : ℝ)|=(4377335299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062672347/2500000000 : ℝ)|^4123 ≤ (500623848861/1562500000000 : ℝ)^3099
        have hw : |(1062672347/2500000000 : ℝ)|=(1062672347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126954601/2500000000 : ℝ)|^4123 ≤ (17321951777551/50000000000000 : ℝ)^3099
        have hw : |(1126954601/2500000000 : ℝ)|=(1126954601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s6_4 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-221014083/1000000000 : ℝ)*x 0 + (263198873/500000000 : ℝ)*x 1 + (84294509/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221014083/1000000000 : ℝ)^4123 ≤ (1677672507967/12500000000000 : ℝ)^3099 := by
    have hnat : (221014083 : ℕ)^4123*12500000000000^3099 ≤ 1677672507967^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221014083 1000000000 1677672507967 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263198873/500000000 : ℝ)^4123 ≤ (10645548741269/25000000000000 : ℝ)^3099 := by
    have hnat : (263198873 : ℕ)^4123*25000000000000^3099 ≤ 10645548741269^3099*500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263198873 500000000 10645548741269 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84294509/156250000 : ℝ)^4123 ≤ (43996424958957/100000000000000 : ℝ)^3099 := by
    have hnat : (84294509 : ℕ)^4123*100000000000000^3099 ≤ 43996424958957^3099*156250000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84294509 156250000 43996424958957 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221014083/1000000000 : ℝ), (263198873/500000000 : ℝ), (84294509/156250000 : ℝ)] ![(1677672507967/12500000000000 : ℝ), (10645548741269/25000000000000 : ℝ), (43996424958957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221014083/1000000000 : ℝ)|^4123 ≤ (1677672507967/12500000000000 : ℝ)^3099
        have hw : |(-221014083/1000000000 : ℝ)|=(221014083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263198873/500000000 : ℝ)|^4123 ≤ (10645548741269/25000000000000 : ℝ)^3099
        have hw : |(263198873/500000000 : ℝ)|=(263198873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84294509/156250000 : ℝ)|^4123 ≤ (43996424958957/100000000000000 : ℝ)^3099
        have hw : |(84294509/156250000 : ℝ)|=(84294509/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s6_5 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664007393/1250000000 : ℝ)*x 0 + (-1072841/5000000 : ℝ)*x 1 + (1348712167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664007393/1250000000 : ℝ)^4123 ≤ (2155022230681/5000000000000 : ℝ)^3099 := by
    have hnat : (664007393 : ℕ)^4123*5000000000000^3099 ≤ 2155022230681^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664007393 1250000000 2155022230681 5000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072841/5000000 : ℝ)^4123 ≤ (6451564712721/50000000000000 : ℝ)^3099 := by
    have hnat : (1072841 : ℕ)^4123*50000000000000^3099 ≤ 6451564712721^3099*5000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072841 5000000 6451564712721 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348712167/2500000000 : ℝ)^4123 ≤ (43996425957157/100000000000000 : ℝ)^3099 := by
    have hnat : (1348712167 : ℕ)^4123*100000000000000^3099 ≤ 43996425957157^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348712167 2500000000 43996425957157 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664007393/1250000000 : ℝ), (-1072841/5000000 : ℝ), (1348712167/2500000000 : ℝ)] ![(2155022230681/5000000000000 : ℝ), (6451564712721/50000000000000 : ℝ), (43996425957157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664007393/1250000000 : ℝ)|^4123 ≤ (2155022230681/5000000000000 : ℝ)^3099
        have hw : |(664007393/1250000000 : ℝ)|=(664007393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072841/5000000 : ℝ)|^4123 ≤ (6451564712721/50000000000000 : ℝ)^3099
        have hw : |(-1072841/5000000 : ℝ)|=(1072841/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348712167/2500000000 : ℝ)|^4123 ≤ (43996425957157/100000000000000 : ℝ)^3099
        have hw : |(1348712167/2500000000 : ℝ)|=(1348712167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s6_6 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656029501/5000000000 : ℝ)*x 0 + (1348712209/2500000000 : ℝ)*x 1 + (-2145681963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656029501/5000000000 : ℝ)^4123 ≤ (43100443080773/100000000000000 : ℝ)^3099 := by
    have hnat : (2656029501 : ℕ)^4123*100000000000000^3099 ≤ 43100443080773^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656029501 5000000000 43100443080773 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348712209/2500000000 : ℝ)^4123 ≤ (21998213889979/50000000000000 : ℝ)^3099 := by
    have hnat : (1348712209 : ℕ)^4123*50000000000000^3099 ≤ 21998213889979^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348712209 2500000000 21998213889979 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145681963/10000000000 : ℝ)^4123 ≤ (12903129129421/100000000000000 : ℝ)^3099 := by
    have hnat : (2145681963 : ℕ)^4123*100000000000000^3099 ≤ 12903129129421^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145681963 10000000000 12903129129421 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656029501/5000000000 : ℝ), (1348712209/2500000000 : ℝ), (-2145681963/10000000000 : ℝ)] ![(43100443080773/100000000000000 : ℝ), (21998213889979/50000000000000 : ℝ), (12903129129421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656029501/5000000000 : ℝ)|^4123 ≤ (43100443080773/100000000000000 : ℝ)^3099
        have hw : |(2656029501/5000000000 : ℝ)|=(2656029501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348712209/2500000000 : ℝ)|^4123 ≤ (21998213889979/50000000000000 : ℝ)^3099
        have hw : |(1348712209/2500000000 : ℝ)|=(1348712209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145681963/10000000000 : ℝ)|^4123 ≤ (12903129129421/100000000000000 : ℝ)^3099
        have hw : |(-2145681963/10000000000 : ℝ)|=(2145681963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s6_7 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2188672813/5000000000 : ℝ)*x 0 + (4507168819/10000000000 : ℝ)*x 1 + (4251341243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188672813/5000000000 : ℝ)^4123 ≤ (166581373393/500000000000 : ℝ)^3099 := by
    have hnat : (2188672813 : ℕ)^4123*500000000000^3099 ≤ 166581373393^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188672813 5000000000 166581373393 500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507168819/10000000000 : ℝ)^4123 ≤ (17318630938563/50000000000000 : ℝ)^3099 := by
    have hnat : (4507168819 : ℕ)^4123*50000000000000^3099 ≤ 17318630938563^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507168819 10000000000 17318630938563 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251341243/10000000000 : ℝ)^4123 ≤ (32046463438723/100000000000000 : ℝ)^3099 := by
    have hnat : (4251341243 : ℕ)^4123*100000000000000^3099 ≤ 32046463438723^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251341243 10000000000 32046463438723 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188672813/5000000000 : ℝ), (4507168819/10000000000 : ℝ), (4251341243/10000000000 : ℝ)] ![(166581373393/500000000000 : ℝ), (17318630938563/50000000000000 : ℝ), (32046463438723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188672813/5000000000 : ℝ)|^4123 ≤ (166581373393/500000000000 : ℝ)^3099
        have hw : |(2188672813/5000000000 : ℝ)|=(2188672813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507168819/10000000000 : ℝ)|^4123 ≤ (17318630938563/50000000000000 : ℝ)^3099
        have hw : |(4507168819/10000000000 : ℝ)|=(4507168819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251341243/10000000000 : ℝ)|^4123 ≤ (32046463438723/100000000000000 : ℝ)^3099
        have hw : |(4251341243/10000000000 : ℝ)|=(4251341243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1053_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11221/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11177/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11177/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11177/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11177/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11177/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11177/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11177/100000 : ℝ) ^ (8245/2048 : ℝ) ≤ (1843243517130781/12500000000000000000 : ℝ) := by
    have hpowers : (11177/100000 : ℝ)^8245 ≤ (1843243517130781/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11177 : ℕ)^8245*12500000000000000000^2048 ≤ 1843243517130781^2048*100000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11177 100000 1843243517130781 12500000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11177/100000 : ℝ)) (X := (1843243517130781/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14053/100000 : ℝ) ^ (8245/2048 : ℝ) ≤ (579217141633957/1562500000000000000 : ℝ) := by
    have hpowers : (14053/100000 : ℝ)^8245 ≤ (579217141633957/1562500000000000000 : ℝ)^2048 := by
      have hnat : (14053 : ℕ)^8245*1562500000000000000^2048 ≤ 579217141633957^2048*100000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14053 100000 579217141633957 1562500000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14053/100000 : ℝ)) (X := (579217141633957/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251843243517130781/6250000000000000000 : ℝ) ≤ (5000366238390299/5000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (6251843243517130781/6250000000000000000 : ℝ)^2048 ≤ (5000366238390299/5000000000000000 : ℝ)^8245 := by
      have hnat : (6251843243517130781 : ℕ)^2048*5000000000000000^8245 ≤ 5000366238390299^8245*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251843243517130781 6250000000000000000 5000366238390299 5000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000366238390299/5000000000000000 : ℝ)) (X := (6251843243517130781/6250000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506476980650202437/12500000000000000000 : ℝ) ≤ (2500321704648719/2500000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (12506476980650202437/12500000000000000000 : ℝ)^2048 ≤ (2500321704648719/2500000000000000 : ℝ)^8245 := by
      have hnat : (12506476980650202437 : ℕ)^2048*2500000000000000^8245 ≤ 2500321704648719^8245*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506476980650202437 12500000000000000000 2500321704648719 2500000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500321704648719/2500000000000000 : ℝ)) (X := (12506476980650202437/12500000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (781829217141633957/781250000000000000 : ℝ) ≤ (5000920580204577/5000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (781829217141633957/781250000000000000 : ℝ)^2048 ≤ (5000920580204577/5000000000000000 : ℝ)^8245 := by
      have hnat : (781829217141633957 : ℕ)^2048*5000000000000000^8245 ≤ 5000920580204577^8245*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781829217141633957 781250000000000000 5000920580204577 5000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000920580204577/5000000000000000 : ℝ)) (X := (781829217141633957/781250000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1843243517130781/12500000000000000000 : ℝ) ≤ ((7187428711576157359/7190000000000000000 : ℝ)+2*(277170907139/143800000000000 : ℝ)*(11177/100000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (7187428711576157359/7190000000000000000 : ℝ)+2*(277170907139/143800000000000 : ℝ)*(11177/100000 : ℝ)=(5000366238390299/5000000000000000 : ℝ) by norm_num, show 1+2*(1843243517130781/12500000000000000000 : ℝ)=(6251843243517130781/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(579217141633957/1562500000000000000 : ℝ)+(1843243517130781/12500000000000000000 : ℝ) ≤ ((7187428711576157359/7190000000000000000 : ℝ)+(277170907139/143800000000000 : ℝ)*((14053/100000 : ℝ)+(11177/100000 : ℝ)))^(8245/2048 : ℝ) := by
    rw [show (7187428711576157359/7190000000000000000 : ℝ)+(277170907139/143800000000000 : ℝ)*((14053/100000 : ℝ)+(11177/100000 : ℝ))=(2500321704648719/2500000000000000 : ℝ) by norm_num, show 1+(579217141633957/1562500000000000000 : ℝ)+(1843243517130781/12500000000000000000 : ℝ)=(12506476980650202437/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(579217141633957/1562500000000000000 : ℝ) ≤ ((7187428711576157359/7190000000000000000 : ℝ)+2*(277170907139/143800000000000 : ℝ)*(14053/100000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (7187428711576157359/7190000000000000000 : ℝ)+2*(277170907139/143800000000000 : ℝ)*(14053/100000 : ℝ)=(5000920580204577/5000000000000000 : ℝ) by norm_num, show 1+2*(579217141633957/1562500000000000000 : ℝ)=(781829217141633957/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7187428711576157359/7190000000000000000 : ℝ)*(X 1 0+X 2 0)+(277170907139/143800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (7187428711576157359/7190000000000000000 : ℝ)) (alpha := (277170907139/143800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7187428711576157359/7190000000000000000 : ℝ)*(X 0 1+X 2 1)+(277170907139/143800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (7187428711576157359/7190000000000000000 : ℝ)) (alpha := (277170907139/143800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7187428711576157359/7190000000000000000 : ℝ)*(X 0 2+X 1 2)+(277170907139/143800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (7187428711576157359/7190000000000000000 : ℝ)) (alpha := (277170907139/143800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-442027111/2000000000 : ℝ)*X 0 0+(5395182101/10000000000 : ℝ)*X 0 1+(5263645171/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534515619/1000000000 : ℝ)*X 1 0+(-2276885457/10000000000 : ℝ)*X 1 1+(5263645171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345156113/10000000000 : ℝ)*X 2 0+(5263645221/10000000000 : ℝ)*X 2 1+(-2276885493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377335299/10000000000 : ℝ)*X 0 0+(1062672347/2500000000 : ℝ)*X 0 1+(1126954601/2500000000 : ℝ)*X 0 2+(4377335299/10000000000 : ℝ)*X 1 0+(1062672347/2500000000 : ℝ)*X 1 1+(1126954601/2500000000 : ℝ)*X 1 2+(4377335299/10000000000 : ℝ)*X 2 0+(1062672347/2500000000 : ℝ)*X 2 1+(1126954601/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-221014083/1000000000 : ℝ)*X 0 0+(263198873/500000000 : ℝ)*X 0 1+(84294509/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664007393/1250000000 : ℝ)*X 1 0+(-1072841/5000000 : ℝ)*X 1 1+(1348712167/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656029501/5000000000 : ℝ)*X 2 0+(1348712209/2500000000 : ℝ)*X 2 1+(-2145681963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2188672813/5000000000 : ℝ)*X 0 0+(4507168819/10000000000 : ℝ)*X 0 1+(4251341243/10000000000 : ℝ)*X 0 2+(2188672813/5000000000 : ℝ)*X 1 0+(4507168819/10000000000 : ℝ)*X 1 1+(4251341243/10000000000 : ℝ)*X 1 2+(2188672813/5000000000 : ℝ)*X 2 0+(4507168819/10000000000 : ℝ)*X 2 1+(4251341243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1586268657591646466978110137/179750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (919543583/50000000000000 : ℝ)*(base19) + (1633096511/100000000000000 : ℝ)*(base23) + (25782889/50000000000000 : ℝ)*(lower2) + (26301469/10000000000000 : ℝ)*(upper3) + (57008437/50000000000000 : ℝ)*(upper5) + (5745838767909781/100000000000000 : ℝ)*(major0) + (5745838767909781/100000000000000 : ℝ)*(major1) + (5745838767909781/100000000000000 : ℝ)*(major2) + (3801240303702687/50000000000000 : ℝ)*(sp0) + (3801262555899487/50000000000000 : ℝ)*(sp1) + (7602525317789629/100000000000000 : ℝ)*(sp2) + (3889122735589329/100000000000000 : ℝ)*(sp3) + (23171740383/50000000000000 : ℝ)*(sp4) + (6888795519/25000000000000 : ℝ)*(sp7) + (777830058154281/20000000000000 : ℝ)*(f.failure) + (380126347544307/5000000000000 : ℝ)*(f.sum) + (26044624715871/7190000000000000000000000000 : ℝ)*base66 + (3268744118129178379/719000000000000000000000000000000 : ℝ)*base67 + (590729623626821621/719000000000000000000000000000000 : ℝ)*base70 + (5046490146333821621/719000000000000000000000000000000 : ℝ)*base72 + (19013435902739/7190000000000000000000000000 : ℝ)*base73 + (3168212603722821621/719000000000000000000000000000000 : ℝ)*base76 + (1584938715556821621/719000000000000000000000000000000 : ℝ)*base78 + (287191083995821621/719000000000000000000000000000000 : ℝ)*base80 + (36871156153029/7190000000000000000000000000 : ℝ)*base81 + (9184729/2000000000000000000000 : ℝ)*base89 + (9184729/2000000000000000000000 : ℝ)*base91 + (9184729/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (507539240024785657072491393/179750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (302731061/50000000000000 : ℝ)*(base19) + (56266607/12500000000000 : ℝ)*(base23) + (8093823/6250000000000 : ℝ)*(upper3) + (166303/1250000000000 : ℝ)*(lower4) + (70981229/100000000000000 : ℝ)*(upper5) + (5774991734269891/100000000000000 : ℝ)*(major0) + (5774991734269891/100000000000000 : ℝ)*(major1) + (5774991734269891/100000000000000 : ℝ)*(major2) + (8369495949/50000000000000 : ℝ)*(sp1) + (5143097917/25000000000000 : ℝ)*(sp2) + (7641100495914363/100000000000000 : ℝ)*(sp4) + (3820541575730171/50000000000000 : ℝ)*(sp5) + (3820539736694919/50000000000000 : ℝ)*(sp6) + (3908882878505939/100000000000000 : ℝ)*(sp7) + (3908882878505939/100000000000000 : ℝ)*(f.failure) + (7641100495914363/100000000000000 : ℝ)*(f.sum) + (18139113005711/7190000000000000000000000000 : ℝ)*base66 + (1078058182685227869/719000000000000000000000000000000 : ℝ)*base67 + (2102658172249227869/719000000000000000000000000000000 : ℝ)*base69 + (2536149658573772131/719000000000000000000000000000000 : ℝ)*base72 + (3575311582399/7190000000000000000000000000 : ℝ)*base73 + (13203405637455227869/719000000000000000000000000000000 : ℝ)*base75 + (6800300963478227869/719000000000000000000000000000000 : ℝ)*base77 + (8703276636381227869/719000000000000000000000000000000 : ℝ)*base79 + (3736438154361/7190000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (64398749/10000000000000000000000 : ℝ)*base90 + (64398749/10000000000000000000000 : ℝ)*base92 + (64398749/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1053_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1053_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1053_s7_0 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210178651/10000000000 : ℝ)*x 0 + (215787523/400000000 : ℝ)*x 1 + (42112887/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210178651/10000000000 : ℝ)^4123 ≤ (838855351779/6250000000000 : ℝ)^3099 := by
    have hnat : (2210178651 : ℕ)^4123*6250000000000^3099 ≤ 838855351779^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210178651 10000000000 838855351779 6250000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215787523/400000000 : ℝ)^4123 ≤ (10998670882767/25000000000000 : ℝ)^3099 := by
    have hnat : (215787523 : ℕ)^4123*25000000000000^3099 ≤ 10998670882767^3099*400000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215787523 400000000 10998670882767 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42112887/80000000 : ℝ)^4123 ≤ (42583630825617/100000000000000 : ℝ)^3099 := by
    have hnat : (42112887 : ℕ)^4123*100000000000000^3099 ≤ 42583630825617^3099*80000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42112887 80000000 42583630825617 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210178651/10000000000 : ℝ), (215787523/400000000 : ℝ), (42112887/80000000 : ℝ)] ![(838855351779/6250000000000 : ℝ), (10998670882767/25000000000000 : ℝ), (42583630825617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210178651/10000000000 : ℝ)|^4123 ≤ (838855351779/6250000000000 : ℝ)^3099
        have hw : |(-2210178651/10000000000 : ℝ)|=(2210178651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215787523/400000000 : ℝ)|^4123 ≤ (10998670882767/25000000000000 : ℝ)^3099
        have hw : |(215787523/400000000 : ℝ)|=(215787523/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42112887/80000000 : ℝ)|^4123 ≤ (42583630825617/100000000000000 : ℝ)^3099
        have hw : |(42112887/80000000 : ℝ)|=(42112887/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s7_1 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334064561/625000000 : ℝ)*x 0 + (-2276434381/10000000000 : ℝ)*x 1 + (2632055483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334064561/625000000 : ℝ)^4123 ≤ (43456751793317/100000000000000 : ℝ)^3099 := by
    have hnat : (334064561 : ℕ)^4123*100000000000000^3099 ≤ 43456751793317^3099*625000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334064561 625000000 43456751793317 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276434381/10000000000 : ℝ)^4123 ≤ (6979808191029/50000000000000 : ℝ)^3099 := by
    have hnat : (2276434381 : ℕ)^4123*50000000000000^3099 ≤ 6979808191029^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276434381 10000000000 6979808191029 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632055483/5000000000 : ℝ)^4123 ≤ (10645907951249/25000000000000 : ℝ)^3099 := by
    have hnat : (2632055483 : ℕ)^4123*25000000000000^3099 ≤ 10645907951249^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632055483 5000000000 10645907951249 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334064561/625000000 : ℝ), (-2276434381/10000000000 : ℝ), (2632055483/5000000000 : ℝ)] ![(43456751793317/100000000000000 : ℝ), (6979808191029/50000000000000 : ℝ), (10645907951249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334064561/625000000 : ℝ)|^4123 ≤ (43456751793317/100000000000000 : ℝ)^3099
        have hw : |(334064561/625000000 : ℝ)|=(334064561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2276434381/10000000000 : ℝ)|^4123 ≤ (6979808191029/50000000000000 : ℝ)^3099
        have hw : |(-2276434381/10000000000 : ℝ)|=(2276434381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632055483/5000000000 : ℝ)|^4123 ≤ (10645907951249/25000000000000 : ℝ)^3099
        have hw : |(2632055483/5000000000 : ℝ)|=(2632055483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s7_2 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672516511/5000000000 : ℝ)*x 0 + (5264110911/10000000000 : ℝ)*x 1 + (-2276434393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672516511/5000000000 : ℝ)^4123 ≤ (4345675229089/10000000000000 : ℝ)^3099 := by
    have hnat : (2672516511 : ℕ)^4123*10000000000000^3099 ≤ 4345675229089^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672516511 5000000000 4345675229089 10000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264110911/10000000000 : ℝ)^4123 ≤ (42583631213063/100000000000000 : ℝ)^3099 := by
    have hnat : (5264110911 : ℕ)^4123*100000000000000^3099 ≤ 42583631213063^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264110911 10000000000 42583631213063 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276434393/10000000000 : ℝ)^4123 ≤ (348990411999/2500000000000 : ℝ)^3099 := by
    have hnat : (2276434393 : ℕ)^4123*2500000000000^3099 ≤ 348990411999^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276434393 10000000000 348990411999 2500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672516511/5000000000 : ℝ), (5264110911/10000000000 : ℝ), (-2276434393/10000000000 : ℝ)] ![(4345675229089/10000000000000 : ℝ), (42583631213063/100000000000000 : ℝ), (348990411999/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672516511/5000000000 : ℝ)|^4123 ≤ (4345675229089/10000000000000 : ℝ)^3099
        have hw : |(2672516511/5000000000 : ℝ)|=(2672516511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264110911/10000000000 : ℝ)|^4123 ≤ (42583631213063/100000000000000 : ℝ)^3099
        have hw : |(5264110911/10000000000 : ℝ)|=(5264110911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2276434393/10000000000 : ℝ)|^4123 ≤ (348990411999/2500000000000 : ℝ)^3099
        have hw : |(-2276434393/10000000000 : ℝ)|=(2276434393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s7_3 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4377359981/10000000000 : ℝ)*x 0 + (2125812127/5000000000 : ℝ)*x 1 + (1126719249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377359981/10000000000 : ℝ)^4123 ≤ (16658210018609/50000000000000 : ℝ)^3099 := by
    have hnat : (4377359981 : ℕ)^4123*50000000000000^3099 ≤ 16658210018609^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377359981 10000000000 16658210018609 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125812127/5000000000 : ℝ)^4123 ≤ (32049301710599/100000000000000 : ℝ)^3099 := by
    have hnat : (2125812127 : ℕ)^4123*100000000000000^3099 ≤ 32049301710599^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125812127 5000000000 32049301710599 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126719249/2500000000 : ℝ)^4123 ≤ (17317139118777/50000000000000 : ℝ)^3099 := by
    have hnat : (1126719249 : ℕ)^4123*50000000000000^3099 ≤ 17317139118777^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126719249 2500000000 17317139118777 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377359981/10000000000 : ℝ), (2125812127/5000000000 : ℝ), (1126719249/2500000000 : ℝ)] ![(16658210018609/50000000000000 : ℝ), (32049301710599/100000000000000 : ℝ), (17317139118777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377359981/10000000000 : ℝ)|^4123 ≤ (16658210018609/50000000000000 : ℝ)^3099
        have hw : |(4377359981/10000000000 : ℝ)|=(4377359981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125812127/5000000000 : ℝ)|^4123 ≤ (32049301710599/100000000000000 : ℝ)^3099
        have hw : |(2125812127/5000000000 : ℝ)|=(2125812127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126719249/2500000000 : ℝ)|^4123 ≤ (17317139118777/50000000000000 : ℝ)^3099
        have hw : |(1126719249/2500000000 : ℝ)|=(1126719249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s7_4 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210183721/10000000000 : ℝ)*x 0 + (2632219173/5000000000 : ℝ)*x 1 + (2697179731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210183721/10000000000 : ℝ)^4123 ≤ (6710863295157/50000000000000 : ℝ)^3099 := by
    have hnat : (2210183721 : ℕ)^4123*50000000000000^3099 ≤ 6710863295157^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210183721 10000000000 6710863295157 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632219173/5000000000 : ℝ)^4123 ≤ (21293577619039/50000000000000 : ℝ)^3099 := by
    have hnat : (2632219173 : ℕ)^4123*50000000000000^3099 ≤ 21293577619039^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632219173 5000000000 21293577619039 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697179731/5000000000 : ℝ)^4123 ≤ (21995559074863/50000000000000 : ℝ)^3099 := by
    have hnat : (2697179731 : ℕ)^4123*50000000000000^3099 ≤ 21995559074863^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697179731 5000000000 21995559074863 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210183721/10000000000 : ℝ), (2632219173/5000000000 : ℝ), (2697179731/5000000000 : ℝ)] ![(6710863295157/50000000000000 : ℝ), (21293577619039/50000000000000 : ℝ), (21995559074863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210183721/10000000000 : ℝ)|^4123 ≤ (6710863295157/50000000000000 : ℝ)^3099
        have hw : |(-2210183721/10000000000 : ℝ)|=(2210183721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632219173/5000000000 : ℝ)|^4123 ≤ (21293577619039/50000000000000 : ℝ)^3099
        have hw : |(2632219173/5000000000 : ℝ)|=(2632219173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697179731/5000000000 : ℝ)|^4123 ≤ (21995559074863/50000000000000 : ℝ)^3099
        have hw : |(2697179731/5000000000 : ℝ)|=(2697179731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s7_5 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062435479/2000000000 : ℝ)*x 0 + (-2146185857/10000000000 : ℝ)*x 1 + (2697179731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062435479/2000000000 : ℝ)^4123 ≤ (5387715137809/12500000000000 : ℝ)^3099 := by
    have hnat : (1062435479 : ℕ)^4123*12500000000000^3099 ≤ 5387715137809^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062435479 2000000000 5387715137809 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146185857/10000000000 : ℝ)^4123 ≤ (12907160729897/100000000000000 : ℝ)^3099 := by
    have hnat : (2146185857 : ℕ)^4123*100000000000000^3099 ≤ 12907160729897^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146185857 10000000000 12907160729897 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697179731/5000000000 : ℝ)^4123 ≤ (21995559074863/50000000000000 : ℝ)^3099 := by
    have hnat : (2697179731 : ℕ)^4123*50000000000000^3099 ≤ 21995559074863^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697179731 5000000000 21995559074863 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062435479/2000000000 : ℝ), (-2146185857/10000000000 : ℝ), (2697179731/5000000000 : ℝ)] ![(5387715137809/12500000000000 : ℝ), (12907160729897/100000000000000 : ℝ), (21995559074863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062435479/2000000000 : ℝ)|^4123 ≤ (5387715137809/12500000000000 : ℝ)^3099
        have hw : |(1062435479/2000000000 : ℝ)|=(1062435479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2146185857/10000000000 : ℝ)|^4123 ≤ (12907160729897/100000000000000 : ℝ)^3099
        have hw : |(-2146185857/10000000000 : ℝ)|=(2146185857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697179731/5000000000 : ℝ)|^4123 ≤ (21995559074863/50000000000000 : ℝ)^3099
        have hw : |(2697179731/5000000000 : ℝ)|=(2697179731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s7_6 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062435479/2000000000 : ℝ)*x 0 + (5394359463/10000000000 : ℝ)*x 1 + (-16767077/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062435479/2000000000 : ℝ)^4123 ≤ (5387715137809/12500000000000 : ℝ)^3099 := by
    have hnat : (1062435479 : ℕ)^4123*12500000000000^3099 ≤ 5387715137809^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062435479 2000000000 5387715137809 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394359463/10000000000 : ℝ)^4123 ≤ (1759644726423/4000000000000 : ℝ)^3099 := by
    have hnat : (5394359463 : ℕ)^4123*4000000000000^3099 ≤ 1759644726423^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394359463 10000000000 1759644726423 4000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16767077/78125000 : ℝ)^4123 ≤ (1613395090237/12500000000000 : ℝ)^3099 := by
    have hnat : (16767077 : ℕ)^4123*12500000000000^3099 ≤ 1613395090237^3099*78125000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16767077 78125000 1613395090237 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062435479/2000000000 : ℝ), (5394359463/10000000000 : ℝ), (-16767077/78125000 : ℝ)] ![(5387715137809/12500000000000 : ℝ), (1759644726423/4000000000000 : ℝ), (1613395090237/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062435479/2000000000 : ℝ)|^4123 ≤ (5387715137809/12500000000000 : ℝ)^3099
        have hw : |(1062435479/2000000000 : ℝ)|=(1062435479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394359463/10000000000 : ℝ)|^4123 ≤ (1759644726423/4000000000000 : ℝ)^3099
        have hw : |(5394359463/10000000000 : ℝ)|=(5394359463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16767077/78125000 : ℝ)|^4123 ≤ (1613395090237/12500000000000 : ℝ)^3099
        have hw : |(-16767077/78125000 : ℝ)|=(16767077/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s7_7 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4377369933/10000000000 : ℝ)*x 0 + (225311849/500000000 : ℝ)*x 1 + (4252266639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377369933/10000000000 : ℝ)^4123 ≤ (6663304162237/20000000000000 : ℝ)^3099 := by
    have hnat : (4377369933 : ℕ)^4123*20000000000000^3099 ≤ 6663304162237^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377369933 10000000000 6663304162237 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225311849/500000000 : ℝ)^4123 ≤ (34627734847097/100000000000000 : ℝ)^3099 := by
    have hnat : (225311849 : ℕ)^4123*100000000000000^3099 ≤ 34627734847097^3099*500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225311849 500000000 34627734847097 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4252266639/10000000000 : ℝ)^4123 ≤ (32055744318283/100000000000000 : ℝ)^3099 := by
    have hnat : (4252266639 : ℕ)^4123*100000000000000^3099 ≤ 32055744318283^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252266639 10000000000 32055744318283 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377369933/10000000000 : ℝ), (225311849/500000000 : ℝ), (4252266639/10000000000 : ℝ)] ![(6663304162237/20000000000000 : ℝ), (34627734847097/100000000000000 : ℝ), (32055744318283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377369933/10000000000 : ℝ)|^4123 ≤ (6663304162237/20000000000000 : ℝ)^3099
        have hw : |(4377369933/10000000000 : ℝ)|=(4377369933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225311849/500000000 : ℝ)|^4123 ≤ (34627734847097/100000000000000 : ℝ)^3099
        have hw : |(225311849/500000000 : ℝ)|=(225311849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4252266639/10000000000 : ℝ)|^4123 ≤ (32055744318283/100000000000000 : ℝ)^3099
        have hw : |(4252266639/10000000000 : ℝ)|=(4252266639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1053_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11231/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13997/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11221/100000 : ℝ) ^ (8245/2048 : ℝ) ≤ (2996208977819721/20000000000000000000 : ℝ) := by
    have hpowers : (11221/100000 : ℝ)^8245 ≤ (2996208977819721/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11221 : ℕ)^8245*20000000000000000000^2048 ≤ 2996208977819721^2048*100000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11221 100000 2996208977819721 20000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11221/100000 : ℝ)) (X := (2996208977819721/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14007/100000 : ℝ) ^ (8245/2048 : ℝ) ≤ (36583803881826793/100000000000000000000 : ℝ) := by
    have hpowers : (14007/100000 : ℝ)^8245 ≤ (36583803881826793/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14007 : ℕ)^8245*100000000000000000000^2048 ≤ 36583803881826793^2048*100000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14007 100000 36583803881826793 100000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14007/100000 : ℝ)) (X := (36583803881826793/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002996208977819721/10000000000000000000 : ℝ) ≤ (1250093019180957/1250000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (10002996208977819721/10000000000000000000 : ℝ)^2048 ≤ (1250093019180957/1250000000000000 : ℝ)^8245 := by
      have hnat : (10002996208977819721 : ℕ)^2048*1250000000000000^8245 ≤ 1250093019180957^8245*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002996208977819721 10000000000000000000 1250093019180957 1250000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250093019180957/1250000000000000 : ℝ)) (X := (10002996208977819721/10000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025782424385462699/50000000000000000000 : ℝ) ≤ (10001280586441191/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (50025782424385462699/50000000000000000000 : ℝ)^2048 ≤ (10001280586441191/10000000000000000 : ℝ)^8245 := by
      have hnat : (50025782424385462699 : ℕ)^2048*10000000000000000^8245 ≤ 10001280586441191^8245*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025782424385462699 50000000000000000000 10001280586441191 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001280586441191/10000000000000000 : ℝ)) (X := (50025782424385462699/50000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036583803881826793/50000000000000000000 : ℝ) ≤ (5000908509717363/5000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (50036583803881826793/50000000000000000000 : ℝ)^2048 ≤ (5000908509717363/5000000000000000 : ℝ)^8245 := by
      have hnat : (50036583803881826793 : ℕ)^2048*5000000000000000^8245 ≤ 5000908509717363^8245*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036583803881826793 50000000000000000000 5000908509717363 5000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000908509717363/5000000000000000 : ℝ)) (X := (50036583803881826793/50000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2996208977819721/20000000000000000000 : ℝ) ≤ ((1989288184447446939/1990000000000000000 : ℝ)+2*(107286598707/55720000000000 : ℝ)*(11221/100000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (1989288184447446939/1990000000000000000 : ℝ)+2*(107286598707/55720000000000 : ℝ)*(11221/100000 : ℝ)=(1250093019180957/1250000000000000 : ℝ) by norm_num, show 1+2*(2996208977819721/20000000000000000000 : ℝ)=(10002996208977819721/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36583803881826793/100000000000000000000 : ℝ)+(2996208977819721/20000000000000000000 : ℝ) ≤ ((1989288184447446939/1990000000000000000 : ℝ)+(107286598707/55720000000000 : ℝ)*((14007/100000 : ℝ)+(11221/100000 : ℝ)))^(8245/2048 : ℝ) := by
    rw [show (1989288184447446939/1990000000000000000 : ℝ)+(107286598707/55720000000000 : ℝ)*((14007/100000 : ℝ)+(11221/100000 : ℝ))=(10001280586441191/10000000000000000 : ℝ) by norm_num, show 1+(36583803881826793/100000000000000000000 : ℝ)+(2996208977819721/20000000000000000000 : ℝ)=(50025782424385462699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36583803881826793/100000000000000000000 : ℝ) ≤ ((1989288184447446939/1990000000000000000 : ℝ)+2*(107286598707/55720000000000 : ℝ)*(14007/100000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (1989288184447446939/1990000000000000000 : ℝ)+2*(107286598707/55720000000000 : ℝ)*(14007/100000 : ℝ)=(5000908509717363/5000000000000000 : ℝ) by norm_num, show 1+2*(36583803881826793/100000000000000000000 : ℝ)=(50036583803881826793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1989288184447446939/1990000000000000000 : ℝ)*(X 1 0+X 2 0)+(107286598707/55720000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (1989288184447446939/1990000000000000000 : ℝ)) (alpha := (107286598707/55720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1989288184447446939/1990000000000000000 : ℝ)*(X 0 1+X 2 1)+(107286598707/55720000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (1989288184447446939/1990000000000000000 : ℝ)) (alpha := (107286598707/55720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1989288184447446939/1990000000000000000 : ℝ)*(X 0 2+X 1 2)+(107286598707/55720000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (1989288184447446939/1990000000000000000 : ℝ)) (alpha := (107286598707/55720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2210178651/10000000000 : ℝ)*X 0 0+(215787523/400000000 : ℝ)*X 0 1+(42112887/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334064561/625000000 : ℝ)*X 1 0+(-2276434381/10000000000 : ℝ)*X 1 1+(2632055483/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672516511/5000000000 : ℝ)*X 2 0+(5264110911/10000000000 : ℝ)*X 2 1+(-2276434393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377359981/10000000000 : ℝ)*X 0 0+(2125812127/5000000000 : ℝ)*X 0 1+(1126719249/2500000000 : ℝ)*X 0 2+(4377359981/10000000000 : ℝ)*X 1 0+(2125812127/5000000000 : ℝ)*X 1 1+(1126719249/2500000000 : ℝ)*X 1 2+(4377359981/10000000000 : ℝ)*X 2 0+(2125812127/5000000000 : ℝ)*X 2 1+(1126719249/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2210183721/10000000000 : ℝ)*X 0 0+(2632219173/5000000000 : ℝ)*X 0 1+(2697179731/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062435479/2000000000 : ℝ)*X 1 0+(-2146185857/10000000000 : ℝ)*X 1 1+(2697179731/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062435479/2000000000 : ℝ)*X 2 0+(5394359463/10000000000 : ℝ)*X 2 1+(-16767077/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377369933/10000000000 : ℝ)*X 0 0+(225311849/500000000 : ℝ)*X 0 1+(4252266639/10000000000 : ℝ)*X 0 2+(4377369933/10000000000 : ℝ)*X 1 0+(225311849/500000000 : ℝ)*X 1 1+(4252266639/10000000000 : ℝ)*X 1 2+(4377369933/10000000000 : ℝ)*X 2 0+(225311849/500000000 : ℝ)*X 2 1+(4252266639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (784132031526162568108511733/99500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (209257357/12500000000000 : ℝ)*(base19) + (830278051/50000000000000 : ℝ)*(base23) + (21222959/50000000000000 : ℝ)*(lower2) + (112261233/50000000000000 : ℝ)*(upper3) + (159381107/100000000000000 : ℝ)*(upper5) + (5788069362190149/100000000000000 : ℝ)*(major0) + (5788069362190149/100000000000000 : ℝ)*(major1) + (5788069362190149/100000000000000 : ℝ)*(major2) + (3829177414053759/50000000000000 : ℝ)*(sp0) + (1531680427226313/20000000000000 : ℝ)*(sp1) + (95730026870429/1250000000000 : ℝ)*(sp2) + (3917709041901607/100000000000000 : ℝ)*(sp3) + (48982082903/100000000000000 : ℝ)*(sp4) + (3201199683/12500000000000 : ℝ)*(sp7) + (3917734651499071/100000000000000 : ℝ)*(f.failure) + (7658403810190421/100000000000000 : ℝ)*(f.sum) + (4010372306063/557200000000000000000000000 : ℝ)*base65 + (606617924220222623/1393000000000000000000000000000000 : ℝ)*base68 + (25684144050194222623/1393000000000000000000000000000000 : ℝ)*base70 + (11521449410989222623/1393000000000000000000000000000000 : ℝ)*base72 + (1213429157161/557200000000000000000000000 : ℝ)*base73 + (3992738391683777377/1393000000000000000000000000000000 : ℝ)*base75 + (2930887142210777377/1393000000000000000000000000000000 : ℝ)*base77 + (35285936914396222623/1393000000000000000000000000000000 : ℝ)*base80 + (1996215393749/557200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (12845839/10000000000000000000000 : ℝ)*base89 + (12845839/10000000000000000000000 : ℝ)*base91 + (12845839/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4267663372574434648761/696500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1144103771/100000000000000 : ℝ)*(base19) + (24898667/2000000000000 : ℝ)*(base23) + (30846589/25000000000000 : ℝ)*(upper3) + (2853039/6250000000000 : ℝ)*(lower4) + (125422931/100000000000000 : ℝ)*(upper5) + (2908611142708587/50000000000000 : ℝ)*(major0) + (2908611142708587/50000000000000 : ℝ)*(major1) + (2908611142708587/50000000000000 : ℝ)*(major2) + (15491415573/50000000000000 : ℝ)*(sp1) + (8347864387/25000000000000 : ℝ)*(sp2) + (7696977156552677/100000000000000 : ℝ)*(sp4) + (48105906435111/625000000000 : ℝ)*(sp5) + (384847126008089/5000000000000 : ℝ)*(sp6) + (1968733605019191/50000000000000 : ℝ)*(sp7) + (1968733605019191/50000000000000 : ℝ)*(f.failure) + (7696977156552677/100000000000000 : ℝ)*(f.sum) + (705191928321/174125000000000000000000000 : ℝ)*base66 + (3436652894914406351/696500000000000000000000000000000 : ℝ)*base67 + (374212553359406351/696500000000000000000000000000000 : ℝ)*base69 + (11335314960835593649/696500000000000000000000000000000 : ℝ)*base72 + (249675574693/1393000000000000000000000000 : ℝ)*base74 + (8169571229296406351/696500000000000000000000000000000 : ℝ)*base75 + (4967708206725593649/696500000000000000000000000000000 : ℝ)*base78 + (4145639819844593649/696500000000000000000000000000000 : ℝ)*base80 + (8421000536213/1393000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (27350919/5000000000000000000000 : ℝ)*base89 + (27350919/5000000000000000000000 : ℝ)*base91 + (27350919/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1053_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1053_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1053_s8_0 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210186469/10000000000 : ℝ)*x 0 + (1078916141/2000000000 : ℝ)*x 1 + (20563333/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210186469/10000000000 : ℝ)^4123 ≤ (2684349758427/20000000000000 : ℝ)^3099 := by
    have hnat : (2210186469 : ℕ)^4123*20000000000000^3099 ≤ 2684349758427^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210186469 10000000000 2684349758427 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078916141/2000000000 : ℝ)^4123 ≤ (43993518581451/100000000000000 : ℝ)^3099 := by
    have hnat : (1078916141 : ℕ)^4123*100000000000000^3099 ≤ 43993518581451^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078916141 2000000000 43993518581451 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20563333/39062500 : ℝ)^4123 ≤ (21292366304533/50000000000000 : ℝ)^3099 := by
    have hnat : (20563333 : ℕ)^4123*50000000000000^3099 ≤ 21292366304533^3099*39062500^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20563333 39062500 21292366304533 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210186469/10000000000 : ℝ), (1078916141/2000000000 : ℝ), (20563333/39062500 : ℝ)] ![(2684349758427/20000000000000 : ℝ), (43993518581451/100000000000000 : ℝ), (21292366304533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210186469/10000000000 : ℝ)|^4123 ≤ (2684349758427/20000000000000 : ℝ)^3099
        have hw : |(-2210186469/10000000000 : ℝ)|=(2210186469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078916141/2000000000 : ℝ)|^4123 ≤ (43993518581451/100000000000000 : ℝ)^3099
        have hw : |(1078916141/2000000000 : ℝ)|=(1078916141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20563333/39062500 : ℝ)|^4123 ≤ (21292366304533/50000000000000 : ℝ)^3099
        have hw : |(20563333/39062500 : ℝ)|=(20563333/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s8_1 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345006677/10000000000 : ℝ)*x 0 + (-1138167161/5000000000 : ℝ)*x 1 + (20563333/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345006677/10000000000 : ℝ)^4123 ≤ (10864116830659/25000000000000 : ℝ)^3099 := by
    have hnat : (5345006677 : ℕ)^4123*25000000000000^3099 ≤ 10864116830659^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345006677 10000000000 10864116830659 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138167161/5000000000 : ℝ)^4123 ≤ (1744850007129/12500000000000 : ℝ)^3099 := by
    have hnat : (1138167161 : ℕ)^4123*12500000000000^3099 ≤ 1744850007129^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138167161 5000000000 1744850007129 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20563333/39062500 : ℝ)^4123 ≤ (21292366304533/50000000000000 : ℝ)^3099 := by
    have hnat : (20563333 : ℕ)^4123*50000000000000^3099 ≤ 21292366304533^3099*39062500^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20563333 39062500 21292366304533 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345006677/10000000000 : ℝ), (-1138167161/5000000000 : ℝ), (20563333/39062500 : ℝ)] ![(10864116830659/25000000000000 : ℝ), (1744850007129/12500000000000 : ℝ), (21292366304533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345006677/10000000000 : ℝ)|^4123 ≤ (10864116830659/25000000000000 : ℝ)^3099
        have hw : |(5345006677/10000000000 : ℝ)|=(5345006677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1138167161/5000000000 : ℝ)|^4123 ≤ (1744850007129/12500000000000 : ℝ)^3099
        have hw : |(-1138167161/5000000000 : ℝ)|=(1138167161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20563333/39062500 : ℝ)|^4123 ≤ (21292366304533/50000000000000 : ℝ)^3099
        have hw : |(20563333/39062500 : ℝ)|=(20563333/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s8_2 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345006677/10000000000 : ℝ)*x 0 + (20563333/39062500 : ℝ)*x 1 + (-1138167161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345006677/10000000000 : ℝ)^4123 ≤ (10864116830659/25000000000000 : ℝ)^3099 := by
    have hnat : (5345006677 : ℕ)^4123*25000000000000^3099 ≤ 10864116830659^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345006677 10000000000 10864116830659 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20563333/39062500 : ℝ)^4123 ≤ (21292366304533/50000000000000 : ℝ)^3099 := by
    have hnat : (20563333 : ℕ)^4123*50000000000000^3099 ≤ 21292366304533^3099*39062500^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20563333 39062500 21292366304533 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1138167161/5000000000 : ℝ)^4123 ≤ (1744850007129/12500000000000 : ℝ)^3099 := by
    have hnat : (1138167161 : ℕ)^4123*12500000000000^3099 ≤ 1744850007129^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138167161 5000000000 1744850007129 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345006677/10000000000 : ℝ), (20563333/39062500 : ℝ), (-1138167161/5000000000 : ℝ)] ![(10864116830659/25000000000000 : ℝ), (21292366304533/50000000000000 : ℝ), (1744850007129/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345006677/10000000000 : ℝ)|^4123 ≤ (10864116830659/25000000000000 : ℝ)^3099
        have hw : |(5345006677/10000000000 : ℝ)|=(5345006677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20563333/39062500 : ℝ)|^4123 ≤ (21292366304533/50000000000000 : ℝ)^3099
        have hw : |(20563333/39062500 : ℝ)|=(20563333/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1138167161/5000000000 : ℝ)|^4123 ≤ (1744850007129/12500000000000 : ℝ)^3099
        have hw : |(-1138167161/5000000000 : ℝ)|=(1138167161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s8_3 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1094341319/2500000000 : ℝ)*x 0 + (2125914263/5000000000 : ℝ)*x 1 + (2253335687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094341319/2500000000 : ℝ)^4123 ≤ (33316473654387/100000000000000 : ℝ)^3099 := by
    have hnat : (1094341319 : ℕ)^4123*100000000000000^3099 ≤ 33316473654387^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094341319 2500000000 33316473654387 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125914263/5000000000 : ℝ)^4123 ≤ (32051350360479/100000000000000 : ℝ)^3099 := by
    have hnat : (2125914263 : ℕ)^4123*100000000000000^3099 ≤ 32051350360479^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125914263 5000000000 32051350360479 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253335687/5000000000 : ℝ)^4123 ≤ (17316087983759/50000000000000 : ℝ)^3099 := by
    have hnat : (2253335687 : ℕ)^4123*50000000000000^3099 ≤ 17316087983759^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253335687 5000000000 17316087983759 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094341319/2500000000 : ℝ), (2125914263/5000000000 : ℝ), (2253335687/5000000000 : ℝ)] ![(33316473654387/100000000000000 : ℝ), (32051350360479/100000000000000 : ℝ), (17316087983759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094341319/2500000000 : ℝ)|^4123 ≤ (33316473654387/100000000000000 : ℝ)^3099
        have hw : |(1094341319/2500000000 : ℝ)|=(1094341319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125914263/5000000000 : ℝ)|^4123 ≤ (32051350360479/100000000000000 : ℝ)^3099
        have hw : |(2125914263/5000000000 : ℝ)|=(2125914263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253335687/5000000000 : ℝ)|^4123 ≤ (17316087983759/50000000000000 : ℝ)^3099
        have hw : |(2253335687/5000000000 : ℝ)|=(2253335687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s8_4 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210191571/10000000000 : ℝ)*x 0 + (2632269801/5000000000 : ℝ)*x 1 + (5394253173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210191571/10000000000 : ℝ)^4123 ≤ (13421790012569/100000000000000 : ℝ)^3099 := by
    have hnat : (2210191571 : ℕ)^4123*100000000000000^3099 ≤ 13421790012569^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210191571 10000000000 13421790012569 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632269801/5000000000 : ℝ)^4123 ≤ (21294122511121/50000000000000 : ℝ)^3099 := by
    have hnat : (2632269801 : ℕ)^4123*50000000000000^3099 ≤ 21294122511121^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632269801 5000000000 21294122511121 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394253173/10000000000 : ℝ)^4123 ≤ (43989964951983/100000000000000 : ℝ)^3099 := by
    have hnat : (5394253173 : ℕ)^4123*100000000000000^3099 ≤ 43989964951983^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394253173 10000000000 43989964951983 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210191571/10000000000 : ℝ), (2632269801/5000000000 : ℝ), (5394253173/10000000000 : ℝ)] ![(13421790012569/100000000000000 : ℝ), (21294122511121/50000000000000 : ℝ), (43989964951983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210191571/10000000000 : ℝ)|^4123 ≤ (13421790012569/100000000000000 : ℝ)^3099
        have hw : |(-2210191571/10000000000 : ℝ)|=(2210191571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632269801/5000000000 : ℝ)|^4123 ≤ (21294122511121/50000000000000 : ℝ)^3099
        have hw : |(2632269801/5000000000 : ℝ)|=(2632269801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394253173/10000000000 : ℝ)|^4123 ≤ (43989964951983/100000000000000 : ℝ)^3099
        have hw : |(5394253173/10000000000 : ℝ)|=(5394253173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s8_5 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328050937/2500000000 : ℝ)*x 0 + (-536573603/2500000000 : ℝ)*x 1 + (5394253187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328050937/2500000000 : ℝ)^4123 ≤ (21551002788773/50000000000000 : ℝ)^3099 := by
    have hnat : (1328050937 : ℕ)^4123*50000000000000^3099 ≤ 21551002788773^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328050937 2500000000 21551002788773 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (536573603/2500000000 : ℝ)^4123 ≤ (2581605861493/20000000000000 : ℝ)^3099 := by
    have hnat : (536573603 : ℕ)^4123*20000000000000^3099 ≤ 2581605861493^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536573603 2500000000 2581605861493 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394253187/10000000000 : ℝ)^4123 ≤ (43989965103877/100000000000000 : ℝ)^3099 := by
    have hnat : (5394253187 : ℕ)^4123*100000000000000^3099 ≤ 43989965103877^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394253187 10000000000 43989965103877 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328050937/2500000000 : ℝ), (-536573603/2500000000 : ℝ), (5394253187/10000000000 : ℝ)] ![(21551002788773/50000000000000 : ℝ), (2581605861493/20000000000000 : ℝ), (43989965103877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328050937/2500000000 : ℝ)|^4123 ≤ (21551002788773/50000000000000 : ℝ)^3099
        have hw : |(1328050937/2500000000 : ℝ)|=(1328050937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-536573603/2500000000 : ℝ)|^4123 ≤ (2581605861493/20000000000000 : ℝ)^3099
        have hw : |(-536573603/2500000000 : ℝ)|=(536573603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394253187/10000000000 : ℝ)|^4123 ≤ (43989965103877/100000000000000 : ℝ)^3099
        have hw : |(5394253187/10000000000 : ℝ)|=(5394253187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s8_6 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312203783/10000000000 : ℝ)*x 0 + (2697126581/5000000000 : ℝ)*x 1 + (-1073147199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312203783/10000000000 : ℝ)^4123 ≤ (10775501488841/25000000000000 : ℝ)^3099 := by
    have hnat : (5312203783 : ℕ)^4123*25000000000000^3099 ≤ 10775501488841^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312203783 10000000000 10775501488841 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697126581/5000000000 : ℝ)^4123 ≤ (43989964832637/100000000000000 : ℝ)^3099 := by
    have hnat : (2697126581 : ℕ)^4123*100000000000000^3099 ≤ 43989964832637^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697126581 5000000000 43989964832637 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073147199/5000000000 : ℝ)^4123 ≤ (12908029195447/100000000000000 : ℝ)^3099 := by
    have hnat : (1073147199 : ℕ)^4123*100000000000000^3099 ≤ 12908029195447^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073147199 5000000000 12908029195447 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312203783/10000000000 : ℝ), (2697126581/5000000000 : ℝ), (-1073147199/5000000000 : ℝ)] ![(10775501488841/25000000000000 : ℝ), (43989964832637/100000000000000 : ℝ), (12908029195447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312203783/10000000000 : ℝ)|^4123 ≤ (10775501488841/25000000000000 : ℝ)^3099
        have hw : |(5312203783/10000000000 : ℝ)|=(5312203783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697126581/5000000000 : ℝ)|^4123 ≤ (43989964832637/100000000000000 : ℝ)^3099
        have hw : |(2697126581/5000000000 : ℝ)|=(2697126581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073147199/5000000000 : ℝ)|^4123 ≤ (12908029195447/100000000000000 : ℝ)^3099
        have hw : |(-1073147199/5000000000 : ℝ)|=(1073147199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s8_7 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (547171909/1250000000 : ℝ)*x 0 + (4506033379/10000000000 : ℝ)*x 1 + (1063117197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547171909/1250000000 : ℝ)^4123 ≤ (33316574873939/100000000000000 : ℝ)^3099 := by
    have hnat : (547171909 : ℕ)^4123*100000000000000^3099 ≤ 33316574873939^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547171909 1250000000 33316574873939 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506033379/10000000000 : ℝ)^4123 ≤ (34625653337203/100000000000000 : ℝ)^3099 := by
    have hnat : (4506033379 : ℕ)^4123*100000000000000^3099 ≤ 34625653337203^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506033379 10000000000 34625653337203 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063117197/2500000000 : ℝ)^4123 ≤ (1282310871103/4000000000000 : ℝ)^3099 := by
    have hnat : (1063117197 : ℕ)^4123*4000000000000^3099 ≤ 1282310871103^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063117197 2500000000 1282310871103 4000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547171909/1250000000 : ℝ), (4506033379/10000000000 : ℝ), (1063117197/2500000000 : ℝ)] ![(33316574873939/100000000000000 : ℝ), (34625653337203/100000000000000 : ℝ), (1282310871103/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547171909/1250000000 : ℝ)|^4123 ≤ (33316574873939/100000000000000 : ℝ)^3099
        have hw : |(547171909/1250000000 : ℝ)|=(547171909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506033379/10000000000 : ℝ)|^4123 ≤ (34625653337203/100000000000000 : ℝ)^3099
        have hw : |(4506033379/10000000000 : ℝ)|=(4506033379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063117197/2500000000 : ℝ)|^4123 ≤ (1282310871103/4000000000000 : ℝ)^3099
        have hw : |(1063117197/2500000000 : ℝ)|=(1063117197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1053_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11233/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2799/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13997/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13997/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13997/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13997/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13997/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13997/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11231/100000 : ℝ) ^ (8245/2048 : ℝ) ≤ (939679156869053/6250000000000000000 : ℝ) := by
    have hpowers : (11231/100000 : ℝ)^8245 ≤ (939679156869053/6250000000000000000 : ℝ)^2048 := by
      have hnat : (11231 : ℕ)^8245*6250000000000000000^2048 ≤ 939679156869053^2048*100000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11231 100000 939679156869053 6250000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11231/100000 : ℝ)) (X := (939679156869053/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13997/100000 : ℝ) ^ (8245/2048 : ℝ) ≤ (36478768572889213/100000000000000000000 : ℝ) := by
    have hpowers : (13997/100000 : ℝ)^8245 ≤ (36478768572889213/100000000000000000000 : ℝ)^2048 := by
      have hnat : (13997 : ℕ)^8245*100000000000000000000^2048 ≤ 36478768572889213^2048*100000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13997 100000 36478768572889213 100000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13997/100000 : ℝ)) (X := (36478768572889213/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125939679156869053/3125000000000000000 : ℝ) ≤ (2500186706656751/2500000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (3125939679156869053/3125000000000000000 : ℝ)^2048 ≤ (2500186706656751/2500000000000000 : ℝ)^8245 := by
      have hnat : (3125939679156869053 : ℕ)^2048*2500000000000000^8245 ≤ 2500186706656751^8245*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125939679156869053 3125000000000000000 2500186706656751 2500000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500186706656751/2500000000000000 : ℝ)) (X := (3125939679156869053/3125000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051513635082794061/100000000000000000000 : ℝ) ≤ (10001279314821763/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (100051513635082794061/100000000000000000000 : ℝ)^2048 ≤ (10001279314821763/10000000000000000 : ℝ)^8245 := by
      have hnat : (100051513635082794061 : ℕ)^2048*10000000000000000^8245 ≤ 10001279314821763^8245*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051513635082794061 100000000000000000000 10001279314821763 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001279314821763/10000000000000000 : ℝ)) (X := (100051513635082794061/100000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036478768572889213/50000000000000000000 : ℝ) ≤ (5000905901508261/5000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (50036478768572889213/50000000000000000000 : ℝ)^2048 ≤ (5000905901508261/5000000000000000 : ℝ)^8245 := by
      have hnat : (50036478768572889213 : ℕ)^2048*5000000000000000^8245 ≤ 5000905901508261^8245*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036478768572889213 50000000000000000000 5000905901508261 5000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000905901508261/5000000000000000 : ℝ)) (X := (50036478768572889213/50000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(939679156869053/6250000000000000000 : ℝ) ≤ ((13825052486309808203/13830000000000000000 : ℝ)+2*(532488194759/276600000000000 : ℝ)*(11231/100000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (13825052486309808203/13830000000000000000 : ℝ)+2*(532488194759/276600000000000 : ℝ)*(11231/100000 : ℝ)=(2500186706656751/2500000000000000 : ℝ) by norm_num, show 1+2*(939679156869053/6250000000000000000 : ℝ)=(3125939679156869053/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36478768572889213/100000000000000000000 : ℝ)+(939679156869053/6250000000000000000 : ℝ) ≤ ((13825052486309808203/13830000000000000000 : ℝ)+(532488194759/276600000000000 : ℝ)*((13997/100000 : ℝ)+(11231/100000 : ℝ)))^(8245/2048 : ℝ) := by
    rw [show (13825052486309808203/13830000000000000000 : ℝ)+(532488194759/276600000000000 : ℝ)*((13997/100000 : ℝ)+(11231/100000 : ℝ))=(10001279314821763/10000000000000000 : ℝ) by norm_num, show 1+(36478768572889213/100000000000000000000 : ℝ)+(939679156869053/6250000000000000000 : ℝ)=(100051513635082794061/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36478768572889213/100000000000000000000 : ℝ) ≤ ((13825052486309808203/13830000000000000000 : ℝ)+2*(532488194759/276600000000000 : ℝ)*(13997/100000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (13825052486309808203/13830000000000000000 : ℝ)+2*(532488194759/276600000000000 : ℝ)*(13997/100000 : ℝ)=(5000905901508261/5000000000000000 : ℝ) by norm_num, show 1+2*(36478768572889213/100000000000000000000 : ℝ)=(50036478768572889213/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13825052486309808203/13830000000000000000 : ℝ)*(X 1 0+X 2 0)+(532488194759/276600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (13997/100000 : ℝ)) (c := (13825052486309808203/13830000000000000000 : ℝ)) (alpha := (532488194759/276600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13825052486309808203/13830000000000000000 : ℝ)*(X 0 1+X 2 1)+(532488194759/276600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (13997/100000 : ℝ)) (c := (13825052486309808203/13830000000000000000 : ℝ)) (alpha := (532488194759/276600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13825052486309808203/13830000000000000000 : ℝ)*(X 0 2+X 1 2)+(532488194759/276600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (13997/100000 : ℝ)) (c := (13825052486309808203/13830000000000000000 : ℝ)) (alpha := (532488194759/276600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2210186469/10000000000 : ℝ)*X 0 0+(1078916141/2000000000 : ℝ)*X 0 1+(20563333/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345006677/10000000000 : ℝ)*X 1 0+(-1138167161/5000000000 : ℝ)*X 1 1+(20563333/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345006677/10000000000 : ℝ)*X 2 0+(20563333/39062500 : ℝ)*X 2 1+(-1138167161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094341319/2500000000 : ℝ)*X 0 0+(2125914263/5000000000 : ℝ)*X 0 1+(2253335687/5000000000 : ℝ)*X 0 2+(1094341319/2500000000 : ℝ)*X 1 0+(2125914263/5000000000 : ℝ)*X 1 1+(2253335687/5000000000 : ℝ)*X 1 2+(1094341319/2500000000 : ℝ)*X 2 0+(2125914263/5000000000 : ℝ)*X 2 1+(2253335687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2210191571/10000000000 : ℝ)*X 0 0+(2632269801/5000000000 : ℝ)*X 0 1+(5394253173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328050937/2500000000 : ℝ)*X 1 0+(-536573603/2500000000 : ℝ)*X 1 1+(5394253187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312203783/10000000000 : ℝ)*X 2 0+(2697126581/5000000000 : ℝ)*X 2 1+(-1073147199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((547171909/1250000000 : ℝ)*X 0 0+(4506033379/10000000000 : ℝ)*X 0 1+(1063117197/2500000000 : ℝ)*X 0 2+(547171909/1250000000 : ℝ)*X 1 0+(4506033379/10000000000 : ℝ)*X 1 1+(1063117197/2500000000 : ℝ)*X 1 2+(547171909/1250000000 : ℝ)*X 2 0+(4506033379/10000000000 : ℝ)*X 2 1+(1063117197/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (565944244795336772730797607/57625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395712541/20000000000000 : ℝ)*(base19) + (921119077/50000000000000 : ℝ)*(base23) + (18216391/25000000000000 : ℝ)*(lower2) + (249415001/100000000000000 : ℝ)*(upper3) + (73890149/50000000000000 : ℝ)*(upper5) + (1449347135422269/25000000000000 : ℝ)*(major0) + (1449347135422269/25000000000000 : ℝ)*(major1) + (1449347135422269/25000000000000 : ℝ)*(major2) + (1917670353476323/25000000000000 : ℝ)*(sp0) + (3835366155325133/50000000000000 : ℝ)*(sp1) + (239710388967963/3125000000000 : ℝ)*(sp2) + (490501653815367/12500000000000 : ℝ)*(sp3) + (52875307677/100000000000000 : ℝ)*(sp4) + (5847254059/20000000000000 : ℝ)*(sp7) + (245252654174577/6250000000000 : ℝ)*(f.failure) + (767073428921297/10000000000000 : ℝ)*(f.sum) + (2804089196509/2305000000000000000000000000 : ℝ)*base65 + (291647406440790869/115250000000000000000000000000000 : ℝ)*base67 + (1302679546625709131/115250000000000000000000000000000 : ℝ)*base70 + (840370029679959131/115250000000000000000000000000000 : ℝ)*base72 + (971013130031/2305000000000000000000000000 : ℝ)*base74 + (1556195712798459131/115250000000000000000000000000000 : ℝ)*base76 + (313395374982540869/115250000000000000000000000000000 : ℝ)*base77 + (110326955007709131/115250000000000000000000000000000 : ℝ)*base80 + (4779989271173/1152500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (3466593/625000000000000000000 : ℝ)*base89 + (3466593/625000000000000000000 : ℝ)*base91 + (3466593/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (489309087411268030338775071/57625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (387361279/25000000000000 : ℝ)*(base19) + (1762324787/100000000000000 : ℝ)*(base23) + (170568551/100000000000000 : ℝ)*(upper3) + (14395381/20000000000000 : ℝ)*(lower4) + (94102897/50000000000000 : ℝ)*(upper5) + (2913265276322443/50000000000000 : ℝ)*(major0) + (2913265276322443/50000000000000 : ℝ)*(major1) + (2913265276322443/50000000000000 : ℝ)*(major2) + (332746119/781250000000 : ℝ)*(sp1) + (46898056779/100000000000000 : ℝ)*(sp2) + (3854646591518253/50000000000000 : ℝ)*(sp4) + (7709249042088157/100000000000000 : ℝ)*(sp5) + (385462226132747/5000000000000 : ℝ)*(sp6) + (492970954901391/12500000000000 : ℝ)*(sp7) + (492970954901391/12500000000000 : ℝ)*(f.failure) + (3854646591518253/50000000000000 : ℝ)*(f.sum) + (14204510003113/6915000000000000000000000000 : ℝ)*base66 + (1268449014193416643/230500000000000000000000000000000 : ℝ)*base67 + (1369626003114416643/230500000000000000000000000000000 : ℝ)*base69 + (449467026437416643/230500000000000000000000000000000 : ℝ)*base71 + (25906752291223/6915000000000000000000000000 : ℝ)*base74 + (1372422824174083357/230500000000000000000000000000000 : ℝ)*base76 + (983568049295916643/230500000000000000000000000000000 : ℝ)*base77 + (865254297463416643/230500000000000000000000000000000 : ℝ)*base79 + (16022062543753/6915000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5730719/1250000000000000000000 : ℝ)*base89 + (5730719/1250000000000000000000 : ℝ)*base91 + (5730719/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1053_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1053_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1053_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1053_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1053_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1053_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1053_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
