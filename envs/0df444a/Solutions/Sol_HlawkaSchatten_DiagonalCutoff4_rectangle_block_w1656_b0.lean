-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1656_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:17:39.899621+00:00
-- url     : https://prove2.me/submissions/0b5f2aeb-d2c9-4d1b-b25d-aadc1db5b2a3

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
theorem support_rectangle_w1656_s0_0 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1482185831/10000000000 : ℝ)*x 0 + (2888956237/5000000000 : ℝ)*x 1 + (2462803253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1482185831/10000000000 : ℝ)^4943 ≤ (9000504693827/100000000000000 : ℝ)^3919 := by
    have hnat : (1482185831 : ℕ)^4943*100000000000000^3919 ≤ 9000504693827^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482185831 10000000000 9000504693827 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2888956237/5000000000 : ℝ)^4943 ≤ (3128987562823/6250000000000 : ℝ)^3919 := by
    have hnat : (2888956237 : ℕ)^4943*6250000000000^3919 ≤ 3128987562823^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2888956237 5000000000 3128987562823 6250000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2462803253/5000000000 : ℝ)^4943 ≤ (8187138857279/20000000000000 : ℝ)^3919 := by
    have hnat : (2462803253 : ℕ)^4943*20000000000000^3919 ≤ 8187138857279^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462803253 5000000000 8187138857279 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1482185831/10000000000 : ℝ), (2888956237/5000000000 : ℝ), (2462803253/5000000000 : ℝ)] ![(9000504693827/100000000000000 : ℝ), (3128987562823/6250000000000 : ℝ), (8187138857279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1482185831/10000000000 : ℝ)|^4943 ≤ (9000504693827/100000000000000 : ℝ)^3919
        have hw : |(-1482185831/10000000000 : ℝ)|=(1482185831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2888956237/5000000000 : ℝ)|^4943 ≤ (3128987562823/6250000000000 : ℝ)^3919
        have hw : |(2888956237/5000000000 : ℝ)|=(2888956237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2462803253/5000000000 : ℝ)|^4943 ≤ (8187138857279/20000000000000 : ℝ)^3919
        have hw : |(2462803253/5000000000 : ℝ)|=(2462803253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s0_1 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5435164897/10000000000 : ℝ)*x 0 + (-1949471361/10000000000 : ℝ)*x 1 + (2462803523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5435164897/10000000000 : ℝ)^4943 ≤ (46347483029677/100000000000000 : ℝ)^3919 := by
    have hnat : (5435164897 : ℕ)^4943*100000000000000^3919 ≤ 46347483029677^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435164897 10000000000 46347483029677 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1949471361/10000000000 : ℝ)^4943 ≤ (1589602126887/12500000000000 : ℝ)^3919 := by
    have hnat : (1949471361 : ℕ)^4943*12500000000000^3919 ≤ 1589602126887^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949471361 10000000000 1589602126887 12500000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2462803523/5000000000 : ℝ)^4943 ≤ (40935699946853/100000000000000 : ℝ)^3919 := by
    have hnat : (2462803523 : ℕ)^4943*100000000000000^3919 ≤ 40935699946853^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462803523 5000000000 40935699946853 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5435164897/10000000000 : ℝ), (-1949471361/10000000000 : ℝ), (2462803523/5000000000 : ℝ)] ![(46347483029677/100000000000000 : ℝ), (1589602126887/12500000000000 : ℝ), (40935699946853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5435164897/10000000000 : ℝ)|^4943 ≤ (46347483029677/100000000000000 : ℝ)^3919
        have hw : |(5435164897/10000000000 : ℝ)|=(5435164897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1949471361/10000000000 : ℝ)|^4943 ≤ (1589602126887/12500000000000 : ℝ)^3919
        have hw : |(-1949471361/10000000000 : ℝ)|=(1949471361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2462803523/5000000000 : ℝ)|^4943 ≤ (40935699946853/100000000000000 : ℝ)^3919
        have hw : |(2462803523/5000000000 : ℝ)|=(2462803523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s0_2 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2717582971/5000000000 : ℝ)*x 0 + (2462803137/5000000000 : ℝ)*x 1 + (-974735489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2717582971/5000000000 : ℝ)^4943 ≤ (46347494269127/100000000000000 : ℝ)^3919 := by
    have hnat : (2717582971 : ℕ)^4943*100000000000000^3919 ≤ 46347494269127^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717582971 5000000000 46347494269127 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2462803137/5000000000 : ℝ)^4943 ≤ (8187138370899/20000000000000 : ℝ)^3919 := by
    have hnat : (2462803137 : ℕ)^4943*20000000000000^3919 ≤ 8187138370899^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462803137 5000000000 8187138370899 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974735489/5000000000 : ℝ)^4943 ≤ (6358406931949/50000000000000 : ℝ)^3919 := by
    have hnat : (974735489 : ℕ)^4943*50000000000000^3919 ≤ 6358406931949^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974735489 5000000000 6358406931949 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2717582971/5000000000 : ℝ), (2462803137/5000000000 : ℝ), (-974735489/5000000000 : ℝ)] ![(46347494269127/100000000000000 : ℝ), (8187138370899/20000000000000 : ℝ), (6358406931949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2717582971/5000000000 : ℝ)|^4943 ≤ (46347494269127/100000000000000 : ℝ)^3919
        have hw : |(2717582971/5000000000 : ℝ)|=(2717582971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2462803137/5000000000 : ℝ)|^4943 ≤ (8187138370899/20000000000000 : ℝ)^3919
        have hw : |(2462803137/5000000000 : ℝ)|=(2462803137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-974735489/5000000000 : ℝ)|^4943 ≤ (6358406931949/50000000000000 : ℝ)^3919
        have hw : |(-974735489/5000000000 : ℝ)|=(974735489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s0_3 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1021954029/2500000000 : ℝ)*x 0 + (1542068837/5000000000 : ℝ)*x 1 + (5305944843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021954029/2500000000 : ℝ)^4943 ≤ (32357687888437/100000000000000 : ℝ)^3919 := by
    have hnat : (1021954029 : ℕ)^4943*100000000000000^3919 ≤ 32357687888437^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021954029 2500000000 32357687888437 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1542068837/5000000000 : ℝ)^4943 ≤ (11340153539513/50000000000000 : ℝ)^3919 := by
    have hnat : (1542068837 : ℕ)^4943*50000000000000^3919 ≤ 11340153539513^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542068837 5000000000 11340153539513 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5305944843/10000000000 : ℝ)^4943 ≤ (44962005012051/100000000000000 : ℝ)^3919 := by
    have hnat : (5305944843 : ℕ)^4943*100000000000000^3919 ≤ 44962005012051^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305944843 10000000000 44962005012051 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1021954029/2500000000 : ℝ), (1542068837/5000000000 : ℝ), (5305944843/10000000000 : ℝ)] ![(32357687888437/100000000000000 : ℝ), (11340153539513/50000000000000 : ℝ), (44962005012051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1021954029/2500000000 : ℝ)|^4943 ≤ (32357687888437/100000000000000 : ℝ)^3919
        have hw : |(1021954029/2500000000 : ℝ)|=(1021954029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1542068837/5000000000 : ℝ)|^4943 ≤ (11340153539513/50000000000000 : ℝ)^3919
        have hw : |(1542068837/5000000000 : ℝ)|=(1542068837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5305944843/10000000000 : ℝ)|^4943 ≤ (44962005012051/100000000000000 : ℝ)^3919
        have hw : |(5305944843/10000000000 : ℝ)|=(5305944843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s0_4 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-742207337/5000000000 : ℝ)*x 0 + (4946680887/10000000000 : ℝ)*x 1 + (719514307/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (742207337/5000000000 : ℝ)^4943 ≤ (4508789524501/50000000000000 : ℝ)^3919 := by
    have hnat : (742207337 : ℕ)^4943*50000000000000^3919 ≤ 4508789524501^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742207337 5000000000 4508789524501 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4946680887/10000000000 : ℝ)^4943 ≤ (8231345247369/20000000000000 : ℝ)^3919 := by
    have hnat : (4946680887 : ℕ)^4943*20000000000000^3919 ≤ 8231345247369^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4946680887 10000000000 8231345247369 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (719514307/1250000000 : ℝ)^4943 ≤ (996513893869/2000000000000 : ℝ)^3919 := by
    have hnat : (719514307 : ℕ)^4943*2000000000000^3919 ≤ 996513893869^3919*1250000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719514307 1250000000 996513893869 2000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-742207337/5000000000 : ℝ), (4946680887/10000000000 : ℝ), (719514307/1250000000 : ℝ)] ![(4508789524501/50000000000000 : ℝ), (8231345247369/20000000000000 : ℝ), (996513893869/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-742207337/5000000000 : ℝ)|^4943 ≤ (4508789524501/50000000000000 : ℝ)^3919
        have hw : |(-742207337/5000000000 : ℝ)|=(742207337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4946680887/10000000000 : ℝ)|^4943 ≤ (8231345247369/20000000000000 : ℝ)^3919
        have hw : |(4946680887/10000000000 : ℝ)|=(4946680887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(719514307/1250000000 : ℝ)|^4943 ≤ (996513893869/2000000000000 : ℝ)^3919
        have hw : |(719514307/1250000000 : ℝ)|=(719514307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s0_5 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1040527207/2000000000 : ℝ)*x 0 + (-1118964159/10000000000 : ℝ)*x 1 + (2878057259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040527207/2000000000 : ℝ)^4943 ≤ (43860658071163/100000000000000 : ℝ)^3919 := by
    have hnat : (1040527207 : ℕ)^4943*100000000000000^3919 ≤ 43860658071163^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040527207 2000000000 43860658071163 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118964159/10000000000 : ℝ)^4943 ≤ (3156823270259/50000000000000 : ℝ)^3919 := by
    have hnat : (1118964159 : ℕ)^4943*50000000000000^3919 ≤ 3156823270259^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118964159 10000000000 3156823270259 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2878057259/5000000000 : ℝ)^4943 ≤ (1245642384259/2500000000000 : ℝ)^3919 := by
    have hnat : (2878057259 : ℕ)^4943*2500000000000^3919 ≤ 1245642384259^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2878057259 5000000000 1245642384259 2500000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040527207/2000000000 : ℝ), (-1118964159/10000000000 : ℝ), (2878057259/5000000000 : ℝ)] ![(43860658071163/100000000000000 : ℝ), (3156823270259/50000000000000 : ℝ), (1245642384259/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040527207/2000000000 : ℝ)|^4943 ≤ (43860658071163/100000000000000 : ℝ)^3919
        have hw : |(1040527207/2000000000 : ℝ)|=(1040527207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118964159/10000000000 : ℝ)|^4943 ≤ (3156823270259/50000000000000 : ℝ)^3919
        have hw : |(-1118964159/10000000000 : ℝ)|=(1118964159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2878057259/5000000000 : ℝ)|^4943 ≤ (1245642384259/2500000000000 : ℝ)^3919
        have hw : |(2878057259/5000000000 : ℝ)|=(2878057259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s0_6 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202636369/10000000000 : ℝ)*x 0 + (2878057223/5000000000 : ℝ)*x 1 + (-111896377/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202636369/10000000000 : ℝ)^4943 ≤ (43860661622677/100000000000000 : ℝ)^3919 := by
    have hnat : (5202636369 : ℕ)^4943*100000000000000^3919 ≤ 43860661622677^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202636369 10000000000 43860661622677 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2878057223/5000000000 : ℝ)^4943 ≤ (49825694584271/100000000000000 : ℝ)^3919 := by
    have hnat : (2878057223 : ℕ)^4943*100000000000000^3919 ≤ 49825694584271^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2878057223 5000000000 49825694584271 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111896377/1000000000 : ℝ)^4943 ≤ (6313643772117/100000000000000 : ℝ)^3919 := by
    have hnat : (111896377 : ℕ)^4943*100000000000000^3919 ≤ 6313643772117^3919*1000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111896377 1000000000 6313643772117 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202636369/10000000000 : ℝ), (2878057223/5000000000 : ℝ), (-111896377/1000000000 : ℝ)] ![(43860661622677/100000000000000 : ℝ), (49825694584271/100000000000000 : ℝ), (6313643772117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202636369/10000000000 : ℝ)|^4943 ≤ (43860661622677/100000000000000 : ℝ)^3919
        have hw : |(5202636369/10000000000 : ℝ)|=(5202636369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2878057223/5000000000 : ℝ)|^4943 ≤ (49825694584271/100000000000000 : ℝ)^3919
        have hw : |(2878057223/5000000000 : ℝ)|=(2878057223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111896377/1000000000 : ℝ)|^4943 ≤ (6313643772117/100000000000000 : ℝ)^3919
        have hw : |(-111896377/1000000000 : ℝ)|=(111896377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s0_7 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (511703431/1250000000 : ℝ)*x 0 + (5251008577/10000000000 : ℝ)*x 1 + (1570481299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511703431/1250000000 : ℝ)^4943 ≤ (32415718585809/100000000000000 : ℝ)^3919 := by
    have hnat : (511703431 : ℕ)^4943*100000000000000^3919 ≤ 32415718585809^3919*1250000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511703431 1250000000 32415718585809 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5251008577/10000000000 : ℝ)^4943 ≤ (8875127996167/20000000000000 : ℝ)^3919 := by
    have hnat : (5251008577 : ℕ)^4943*20000000000000^3919 ≤ 8875127996167^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251008577 10000000000 8875127996167 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1570481299/5000000000 : ℝ)^4943 ≤ (23208641417627/100000000000000 : ℝ)^3919 := by
    have hnat : (1570481299 : ℕ)^4943*100000000000000^3919 ≤ 23208641417627^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570481299 5000000000 23208641417627 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(511703431/1250000000 : ℝ), (5251008577/10000000000 : ℝ), (1570481299/5000000000 : ℝ)] ![(32415718585809/100000000000000 : ℝ), (8875127996167/20000000000000 : ℝ), (23208641417627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(511703431/1250000000 : ℝ)|^4943 ≤ (32415718585809/100000000000000 : ℝ)^3919
        have hw : |(511703431/1250000000 : ℝ)|=(511703431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5251008577/10000000000 : ℝ)|^4943 ≤ (8875127996167/20000000000000 : ℝ)^3919
        have hw : |(5251008577/10000000000 : ℝ)|=(5251008577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1570481299/5000000000 : ℝ)|^4943 ≤ (23208641417627/100000000000000 : ℝ)^3919
        have hw : |(1570481299/5000000000 : ℝ)|=(1570481299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1656_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4959/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2323/10000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4939/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4939 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4939*1^1024 ≤ 0^1024*1^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4939/1024 : ℝ) ≤ (602017292765060533/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4939 ≤ (602017292765060533/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4939*50000000000000000000^1024 ≤ 602017292765060533^1024*5^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 602017292765060533 50000000000000000000 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (602017292765060533/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4939 := by
      have hnat : (1 : ℕ)^1024*1^4939 ≤ 1^4939*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50602017292765060533/50000000000000000000 : ℝ) ≤ (313276403262329/312500000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (50602017292765060533/50000000000000000000 : ℝ)^1024 ≤ (313276403262329/312500000000000 : ℝ)^4939 := by
      have hnat : (50602017292765060533 : ℕ)^1024*312500000000000^4939 ≤ 313276403262329^4939*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50602017292765060533 50000000000000000000 313276403262329 312500000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313276403262329/312500000000000 : ℝ)) (X := (50602017292765060533/50000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25602017292765060533/25000000000000000000 : ℝ) ≤ (157026403262329/156250000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (25602017292765060533/25000000000000000000 : ℝ)^1024 ≤ (157026403262329/156250000000000 : ℝ)^4939 := by
      have hnat : (25602017292765060533 : ℕ)^1024*156250000000000^4939 ≤ 157026403262329^4939*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25602017292765060533 25000000000000000000 157026403262329 156250000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (157026403262329/156250000000000 : ℝ)) (X := (25602017292765060533/25000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(776403262329/125000000000000 : ℝ)*(0 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(776403262329/125000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(602017292765060533/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(776403262329/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4939/1024 : ℝ) := by
    rw [show (1 : ℝ)+(776403262329/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(313276403262329/312500000000000 : ℝ) by norm_num, show 1+(602017292765060533/50000000000000000000 : ℝ)+(0 : ℝ)=(50602017292765060533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(602017292765060533/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(776403262329/125000000000000 : ℝ)*(2/5 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(776403262329/125000000000000 : ℝ)*(2/5 : ℝ)=(157026403262329/156250000000000 : ℝ) by norm_num, show 1+2*(602017292765060533/50000000000000000000 : ℝ)=(25602017292765060533/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(776403262329/125000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (776403262329/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(776403262329/125000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (776403262329/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(776403262329/125000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (776403262329/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1482185831/10000000000 : ℝ)*X 0 0+(2888956237/5000000000 : ℝ)*X 0 1+(2462803253/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5435164897/10000000000 : ℝ)*X 1 0+(-1949471361/10000000000 : ℝ)*X 1 1+(2462803523/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2717582971/5000000000 : ℝ)*X 2 0+(2462803137/5000000000 : ℝ)*X 2 1+(-974735489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1021954029/2500000000 : ℝ)*X 0 0+(1542068837/5000000000 : ℝ)*X 0 1+(5305944843/10000000000 : ℝ)*X 0 2+(1021954029/2500000000 : ℝ)*X 1 0+(1542068837/5000000000 : ℝ)*X 1 1+(5305944843/10000000000 : ℝ)*X 1 2+(1021954029/2500000000 : ℝ)*X 2 0+(1542068837/5000000000 : ℝ)*X 2 1+(5305944843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-742207337/5000000000 : ℝ)*X 0 0+(4946680887/10000000000 : ℝ)*X 0 1+(719514307/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1040527207/2000000000 : ℝ)*X 1 0+(-1118964159/10000000000 : ℝ)*X 1 1+(2878057259/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5202636369/10000000000 : ℝ)*X 2 0+(2878057223/5000000000 : ℝ)*X 2 1+(-111896377/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((511703431/1250000000 : ℝ)*X 0 0+(5251008577/10000000000 : ℝ)*X 0 1+(1570481299/5000000000 : ℝ)*X 0 2+(511703431/1250000000 : ℝ)*X 1 0+(5251008577/10000000000 : ℝ)*X 1 1+(1570481299/5000000000 : ℝ)*X 1 2+(511703431/1250000000 : ℝ)*X 2 0+(5251008577/10000000000 : ℝ)*X 2 1+(1570481299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (666196167534603187563/97656250000000000000000000 : ℝ) := by norm_num
    linear_combination (142939043/100000000000000 : ℝ)*(base1) + (636949599/50000000000000 : ℝ)*(base19) + (187435619/12500000000000 : ℝ)*(base23) + (865247/1250000000000 : ℝ)*(upper3) + (257231601/100000000000000 : ℝ)*(upper5) + (202923484279221/25000000000000 : ℝ)*(major0) + (202923484279221/25000000000000 : ℝ)*(major1) + (202923484279221/25000000000000 : ℝ)*(major2) + (586646083249507/50000000000000 : ℝ)*(sp0) + (1173297614841809/100000000000000 : ℝ)*(sp1) + (586648694628027/50000000000000 : ℝ)*(sp2) + (450086509622819/100000000000000 : ℝ)*(sp3) + (1716295259/25000000000000 : ℝ)*(sp4) + (2105535933/100000000000000 : ℝ)*(sp7) + (112522189524449/25000000000000 : ℝ)*(f.failure) + (586649444370503/50000000000000 : ℝ)*(f.sum) + (34694197263/48828125000000000000000000 : ℝ)*base66 + (15522788984333/1562500000000000000000000000 : ℝ)*base68 + (3297488884333/1562500000000000000000000000 : ℝ)*base70 + (4406221637479/781250000000000000000000000 : ℝ)*base72 + (1076108737479/390625000000000000000000000 : ℝ)*base74 + (6030107499979/781250000000000000000000000 : ℝ)*base76 + (1791555909291/3125000000000000000000000000 : ℝ)*base78 + (8178294028083/1562500000000000000000000000 : ℝ)*base80 + (2076576222043/3125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1184307/125000000000000000000 : ℝ)*base89 + (1184307/125000000000000000000 : ℝ)*base91 + (1184307/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11672138010904319300673/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (84155683/100000000000000 : ℝ)*(base1) + (14567263/2000000000000 : ℝ)*(base19) + (860941921/100000000000000 : ℝ)*(base23) + (227148717/100000000000000 : ℝ)*(base32) + (146156289/100000000000000 : ℝ)*(upper3) + (213669238865179/25000000000000 : ℝ)*(major0) + (213669238865179/25000000000000 : ℝ)*(major1) + (213669238865179/25000000000000 : ℝ)*(major2) + (1471044987/100000000000000 : ℝ)*(sp1) + (2662826811/100000000000000 : ℝ)*(sp2) + (617715333798131/50000000000000 : ℝ)*(sp4) + (617714192016221/50000000000000 : ℝ)*(sp5) + (154428382458981/12500000000000 : ℝ)*(sp6) + (118480691792709/25000000000000 : ℝ)*(sp7) + (118480769618809/25000000000000 : ℝ)*(f.failure) + (1235430583440579/100000000000000 : ℝ)*(f.sum) + (1814033739359/1562500000000000000000000000 : ℝ)*base66 + (6432448148141/3125000000000000000000000000 : ℝ)*base67 + (21139164916891/3125000000000000000000000000 : ℝ)*base69 + (8161738806883/1562500000000000000000000000 : ℝ)*base71 + (5301626375593/3125000000000000000000000000 : ℝ)*base74 + (1547109726859/3125000000000000000000000000 : ℝ)*base76 + (1156028839359/3125000000000000000000000000 : ℝ)*base78 + (11259064439359/3125000000000000000000000000 : ℝ)*base80 + (3208376981883/781250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (638213/125000000000000000000 : ℝ)*base90 + (638213/125000000000000000000 : ℝ)*base92 + (638213/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1656_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4959/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2323/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1656_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1656_s1_0 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-158561041/1000000000 : ℝ)*x 0 + (5491840833/10000000000 : ℝ)*x 1 + (5144403651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158561041/1000000000 : ℝ)^4943 ≤ (122496851289/1250000000000 : ℝ)^3919 := by
    have hnat : (158561041 : ℕ)^4943*1250000000000^3919 ≤ 122496851289^3919*1000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158561041 1000000000 122496851289 1250000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491840833/10000000000 : ℝ)^4943 ≤ (46957886810417/100000000000000 : ℝ)^3919 := by
    have hnat : (5491840833 : ℕ)^4943*100000000000000^3919 ≤ 46957886810417^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491840833 10000000000 46957886810417 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5144403651/10000000000 : ℝ)^4943 ≤ (21621182541137/50000000000000 : ℝ)^3919 := by
    have hnat : (5144403651 : ℕ)^4943*50000000000000^3919 ≤ 21621182541137^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144403651 10000000000 21621182541137 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-158561041/1000000000 : ℝ), (5491840833/10000000000 : ℝ), (5144403651/10000000000 : ℝ)] ![(122496851289/1250000000000 : ℝ), (46957886810417/100000000000000 : ℝ), (21621182541137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-158561041/1000000000 : ℝ)|^4943 ≤ (122496851289/1250000000000 : ℝ)^3919
        have hw : |(-158561041/1000000000 : ℝ)|=(158561041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491840833/10000000000 : ℝ)|^4943 ≤ (46957886810417/100000000000000 : ℝ)^3919
        have hw : |(5491840833/10000000000 : ℝ)|=(5491840833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5144403651/10000000000 : ℝ)|^4943 ≤ (21621182541137/50000000000000 : ℝ)^3919
        have hw : |(5144403651/10000000000 : ℝ)|=(5144403651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s1_1 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359072267/10000000000 : ℝ)*x 0 + (-883048523/5000000000 : ℝ)*x 1 + (128610087/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359072267/10000000000 : ℝ)^4943 ≤ (45530574295671/100000000000000 : ℝ)^3919 := by
    have hnat : (5359072267 : ℕ)^4943*100000000000000^3919 ≤ 45530574295671^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359072267 10000000000 45530574295671 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883048523/5000000000 : ℝ)^4943 ≤ (5613531205543/50000000000000 : ℝ)^3919 := by
    have hnat : (883048523 : ℕ)^4943*50000000000000^3919 ≤ 5613531205543^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883048523 5000000000 5613531205543 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128610087/250000000 : ℝ)^4943 ≤ (10810590817331/25000000000000 : ℝ)^3919 := by
    have hnat : (128610087 : ℕ)^4943*25000000000000^3919 ≤ 10810590817331^3919*250000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128610087 250000000 10810590817331 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359072267/10000000000 : ℝ), (-883048523/5000000000 : ℝ), (128610087/250000000 : ℝ)] ![(45530574295671/100000000000000 : ℝ), (5613531205543/50000000000000 : ℝ), (10810590817331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359072267/10000000000 : ℝ)|^4943 ≤ (45530574295671/100000000000000 : ℝ)^3919
        have hw : |(5359072267/10000000000 : ℝ)|=(5359072267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-883048523/5000000000 : ℝ)|^4943 ≤ (5613531205543/50000000000000 : ℝ)^3919
        have hw : |(-883048523/5000000000 : ℝ)|=(883048523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128610087/250000000 : ℝ)|^4943 ≤ (10810590817331/25000000000000 : ℝ)^3919
        have hw : |(128610087/250000000 : ℝ)|=(128610087/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s1_2 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359071719/10000000000 : ℝ)*x 0 + (2572202033/5000000000 : ℝ)*x 1 + (-883048503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359071719/10000000000 : ℝ)^4943 ≤ (9106113684671/20000000000000 : ℝ)^3919 := by
    have hnat : (5359071719 : ℕ)^4943*20000000000000^3919 ≤ 9106113684671^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359071719 10000000000 9106113684671 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2572202033/5000000000 : ℝ)^4943 ≤ (10810592370531/25000000000000 : ℝ)^3919 := by
    have hnat : (2572202033 : ℕ)^4943*25000000000000^3919 ≤ 10810592370531^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572202033 5000000000 10810592370531 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883048503/5000000000 : ℝ)^4943 ≤ (5613531045183/50000000000000 : ℝ)^3919 := by
    have hnat : (883048503 : ℕ)^4943*50000000000000^3919 ≤ 5613531045183^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883048503 5000000000 5613531045183 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359071719/10000000000 : ℝ), (2572202033/5000000000 : ℝ), (-883048503/5000000000 : ℝ)] ![(9106113684671/20000000000000 : ℝ), (10810592370531/25000000000000 : ℝ), (5613531045183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359071719/10000000000 : ℝ)|^4943 ≤ (9106113684671/20000000000000 : ℝ)^3919
        have hw : |(5359071719/10000000000 : ℝ)|=(5359071719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2572202033/5000000000 : ℝ)|^4943 ≤ (10810592370531/25000000000000 : ℝ)^3919
        have hw : |(2572202033/5000000000 : ℝ)|=(2572202033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-883048503/5000000000 : ℝ)|^4943 ≤ (5613531045183/50000000000000 : ℝ)^3919
        have hw : |(-883048503/5000000000 : ℝ)|=(883048503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s1_3 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2084599339/5000000000 : ℝ)*x 0 + (1866995137/5000000000 : ℝ)*x 1 + (1159923911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084599339/5000000000 : ℝ)^4943 ≤ (16586154328171/50000000000000 : ℝ)^3919 := by
    have hnat : (2084599339 : ℕ)^4943*50000000000000^3919 ≤ 16586154328171^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084599339 5000000000 16586154328171 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866995137/5000000000 : ℝ)^4943 ≤ (28865947875773/100000000000000 : ℝ)^3919 := by
    have hnat : (1866995137 : ℕ)^4943*100000000000000^3919 ≤ 28865947875773^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866995137 5000000000 28865947875773 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1159923911/2500000000 : ℝ)^4943 ≤ (9490435864311/25000000000000 : ℝ)^3919 := by
    have hnat : (1159923911 : ℕ)^4943*25000000000000^3919 ≤ 9490435864311^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159923911 2500000000 9490435864311 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2084599339/5000000000 : ℝ), (1866995137/5000000000 : ℝ), (1159923911/2500000000 : ℝ)] ![(16586154328171/50000000000000 : ℝ), (28865947875773/100000000000000 : ℝ), (9490435864311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2084599339/5000000000 : ℝ)|^4943 ≤ (16586154328171/50000000000000 : ℝ)^3919
        have hw : |(2084599339/5000000000 : ℝ)|=(2084599339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1866995137/5000000000 : ℝ)|^4943 ≤ (28865947875773/100000000000000 : ℝ)^3919
        have hw : |(1866995137/5000000000 : ℝ)|=(1866995137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1159923911/2500000000 : ℝ)|^4943 ≤ (9490435864311/25000000000000 : ℝ)^3919
        have hw : |(1159923911/2500000000 : ℝ)|=(1159923911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s1_4 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-396439697/2500000000 : ℝ)*x 0 + (64348707/125000000 : ℝ)*x 1 + (686037401/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396439697/2500000000 : ℝ)^4943 ≤ (9800904770781/100000000000000 : ℝ)^3919 := by
    have hnat : (396439697 : ℕ)^4943*100000000000000^3919 ≤ 9800904770781^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396439697 2500000000 9800904770781 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64348707/125000000 : ℝ)^4943 ≤ (21639700176997/50000000000000 : ℝ)^3919 := by
    have hnat : (64348707 : ℕ)^4943*50000000000000^3919 ≤ 21639700176997^3919*125000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64348707 125000000 21639700176997 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686037401/1250000000 : ℝ)^4943 ≤ (23459847426081/50000000000000 : ℝ)^3919 := by
    have hnat : (686037401 : ℕ)^4943*50000000000000^3919 ≤ 23459847426081^3919*1250000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686037401 1250000000 23459847426081 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396439697/2500000000 : ℝ), (64348707/125000000 : ℝ), (686037401/1250000000 : ℝ)] ![(9800904770781/100000000000000 : ℝ), (21639700176997/50000000000000 : ℝ), (23459847426081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396439697/2500000000 : ℝ)|^4943 ≤ (9800904770781/100000000000000 : ℝ)^3919
        have hw : |(-396439697/2500000000 : ℝ)|=(396439697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64348707/125000000 : ℝ)|^4943 ≤ (21639700176997/50000000000000 : ℝ)^3919
        have hw : |(64348707/125000000 : ℝ)|=(64348707/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686037401/1250000000 : ℝ)|^4943 ≤ (23459847426081/50000000000000 : ℝ)^3919
        have hw : |(686037401/1250000000 : ℝ)|=(686037401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s1_5 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266120069/10000000000 : ℝ)*x 0 + (-1422201489/10000000000 : ℝ)*x 1 + (2744149627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266120069/10000000000 : ℝ)^4943 ≤ (173971774151/390625000000 : ℝ)^3919 := by
    have hnat : (5266120069 : ℕ)^4943*390625000000^3919 ≤ 173971774151^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266120069 10000000000 173971774151 390625000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1422201489/10000000000 : ℝ)^4943 ≤ (4271765227957/50000000000000 : ℝ)^3919 := by
    have hnat : (1422201489 : ℕ)^4943*50000000000000^3919 ≤ 4271765227957^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422201489 10000000000 4271765227957 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744149627/5000000000 : ℝ)^4943 ≤ (11729923837043/25000000000000 : ℝ)^3919 := by
    have hnat : (2744149627 : ℕ)^4943*25000000000000^3919 ≤ 11729923837043^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744149627 5000000000 11729923837043 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266120069/10000000000 : ℝ), (-1422201489/10000000000 : ℝ), (2744149627/5000000000 : ℝ)] ![(173971774151/390625000000 : ℝ), (4271765227957/50000000000000 : ℝ), (11729923837043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266120069/10000000000 : ℝ)|^4943 ≤ (173971774151/390625000000 : ℝ)^3919
        have hw : |(5266120069/10000000000 : ℝ)|=(5266120069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1422201489/10000000000 : ℝ)|^4943 ≤ (4271765227957/50000000000000 : ℝ)^3919
        have hw : |(-1422201489/10000000000 : ℝ)|=(1422201489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744149627/5000000000 : ℝ)|^4943 ≤ (11729923837043/25000000000000 : ℝ)^3919
        have hw : |(2744149627/5000000000 : ℝ)|=(2744149627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s1_6 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633059923/5000000000 : ℝ)*x 0 + (171509361/312500000 : ℝ)*x 1 + (-711100689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633059923/5000000000 : ℝ)^4943 ≤ (4453677180391/10000000000000 : ℝ)^3919 := by
    have hnat : (2633059923 : ℕ)^4943*10000000000000^3919 ≤ 4453677180391^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633059923 5000000000 4453677180391 10000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171509361/312500000 : ℝ)^4943 ≤ (2932481160091/6250000000000 : ℝ)^3919 := by
    have hnat : (171509361 : ℕ)^4943*6250000000000^3919 ≤ 2932481160091^3919*312500000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171509361 312500000 2932481160091 6250000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (711100689/5000000000 : ℝ)^4943 ≤ (4271764807439/50000000000000 : ℝ)^3919 := by
    have hnat : (711100689 : ℕ)^4943*50000000000000^3919 ≤ 4271764807439^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711100689 5000000000 4271764807439 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633059923/5000000000 : ℝ), (171509361/312500000 : ℝ), (-711100689/5000000000 : ℝ)] ![(4453677180391/10000000000000 : ℝ), (2932481160091/6250000000000 : ℝ), (4271764807439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633059923/5000000000 : ℝ)|^4943 ≤ (4453677180391/10000000000000 : ℝ)^3919
        have hw : |(2633059923/5000000000 : ℝ)|=(2633059923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171509361/312500000 : ℝ)|^4943 ≤ (2932481160091/6250000000000 : ℝ)^3919
        have hw : |(171509361/312500000 : ℝ)|=(171509361/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-711100689/5000000000 : ℝ)|^4943 ≤ (4271764807439/50000000000000 : ℝ)^3919
        have hw : |(-711100689/5000000000 : ℝ)|=(711100689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s1_7 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4169585809/10000000000 : ℝ)*x 0 + (46305907/100000000 : ℝ)*x 1 + (1871611457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169585809/10000000000 : ℝ)^4943 ≤ (16588096875797/50000000000000 : ℝ)^3919 := by
    have hnat : (4169585809 : ℕ)^4943*50000000000000^3919 ≤ 16588096875797^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169585809 10000000000 16588096875797 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46305907/100000000 : ℝ)^4943 ≤ (18933903100471/50000000000000 : ℝ)^3919 := by
    have hnat : (46305907 : ℕ)^4943*50000000000000^3919 ≤ 18933903100471^3919*100000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46305907 100000000 18933903100471 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1871611457/5000000000 : ℝ)^4943 ≤ (28956000023093/100000000000000 : ℝ)^3919 := by
    have hnat : (1871611457 : ℕ)^4943*100000000000000^3919 ≤ 28956000023093^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871611457 5000000000 28956000023093 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169585809/10000000000 : ℝ), (46305907/100000000 : ℝ), (1871611457/5000000000 : ℝ)] ![(16588096875797/50000000000000 : ℝ), (18933903100471/50000000000000 : ℝ), (28956000023093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169585809/10000000000 : ℝ)|^4943 ≤ (16588096875797/50000000000000 : ℝ)^3919
        have hw : |(4169585809/10000000000 : ℝ)|=(4169585809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46305907/100000000 : ℝ)|^4943 ≤ (18933903100471/50000000000000 : ℝ)^3919
        have hw : |(46305907/100000000 : ℝ)|=(46305907/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1871611457/5000000000 : ℝ)|^4943 ≤ (28956000023093/100000000000000 : ℝ)^3919
        have hw : |(1871611457/5000000000 : ℝ)|=(1871611457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1656_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2323/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4959/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9837/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8611/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2323/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4959/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2323/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4959/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2323/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4959/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2323/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4959/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2323/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4959/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2323/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4959/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4959/100000 : ℝ) ^ (4939/1024 : ℝ) ≤ (50999958775651/100000000000000000000 : ℝ) := by
    have hpowers : (4959/100000 : ℝ)^4939 ≤ (50999958775651/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4959 : ℕ)^4939*100000000000000000000^1024 ≤ 50999958775651^1024*100000^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4959 100000 50999958775651 100000000000000000000 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4959/100000 : ℝ)) (X := (50999958775651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2323/10000 : ℝ) ^ (4939/1024 : ℝ) ≤ (21889800957824669/25000000000000000000 : ℝ) := by
    have hpowers : (2323/10000 : ℝ)^4939 ≤ (21889800957824669/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2323 : ℕ)^4939*25000000000000000000^1024 ≤ 21889800957824669^1024*10000^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2323 10000 21889800957824669 25000000000000000000 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2323/10000 : ℝ)) (X := (21889800957824669/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000050999958775651/50000000000000000000 : ℝ) ≤ (10000002114757509/10000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (50000050999958775651/50000000000000000000 : ℝ)^1024 ≤ (10000002114757509/10000000000000000 : ℝ)^4939 := by
      have hnat : (50000050999958775651 : ℕ)^1024*10000000000000000^4939 ≤ 10000002114757509^4939*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000050999958775651 50000000000000000000 10000002114757509 10000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002114757509/10000000000000000 : ℝ)) (X := (50000050999958775651/50000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100087610203790074327/100000000000000000000 : ℝ) ≤ (5000907893439693/5000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (100087610203790074327/100000000000000000000 : ℝ)^1024 ≤ (5000907893439693/5000000000000000 : ℝ)^4939 := by
      have hnat : (100087610203790074327 : ℕ)^1024*5000000000000000^4939 ≤ 5000907893439693^4939*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100087610203790074327 100000000000000000000 5000907893439693 5000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000907893439693/5000000000000000 : ℝ)) (X := (100087610203790074327/100000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12521889800957824669/12500000000000000000 : ℝ) ≤ (10003629459001263/10000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (12521889800957824669/12500000000000000000 : ℝ)^1024 ≤ (10003629459001263/10000000000000000 : ℝ)^4939 := by
      have hnat : (12521889800957824669 : ℕ)^1024*10000000000000000^4939 ≤ 10003629459001263^4939*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12521889800957824669 12500000000000000000 10003629459001263 10000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003629459001263/10000000000000000 : ℝ)) (X := (12521889800957824669/12500000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(50999958775651/100000000000000000000 : ℝ) ≤ ((16608368239875424623/16610000000000000000 : ℝ)+2*(164879283807/166100000000000 : ℝ)*(4959/100000 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (16608368239875424623/16610000000000000000 : ℝ)+2*(164879283807/166100000000000 : ℝ)*(4959/100000 : ℝ)=(10000002114757509/10000000000000000 : ℝ) by norm_num, show 1+2*(50999958775651/100000000000000000000 : ℝ)=(50000050999958775651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21889800957824669/25000000000000000000 : ℝ)+(50999958775651/100000000000000000000 : ℝ) ≤ ((16608368239875424623/16610000000000000000 : ℝ)+(164879283807/166100000000000 : ℝ)*((2323/10000 : ℝ)+(4959/100000 : ℝ)))^(4939/1024 : ℝ) := by
    rw [show (16608368239875424623/16610000000000000000 : ℝ)+(164879283807/166100000000000 : ℝ)*((2323/10000 : ℝ)+(4959/100000 : ℝ))=(5000907893439693/5000000000000000 : ℝ) by norm_num, show 1+(21889800957824669/25000000000000000000 : ℝ)+(50999958775651/100000000000000000000 : ℝ)=(100087610203790074327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21889800957824669/25000000000000000000 : ℝ) ≤ ((16608368239875424623/16610000000000000000 : ℝ)+2*(164879283807/166100000000000 : ℝ)*(2323/10000 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (16608368239875424623/16610000000000000000 : ℝ)+2*(164879283807/166100000000000 : ℝ)*(2323/10000 : ℝ)=(10003629459001263/10000000000000000 : ℝ) by norm_num, show 1+2*(21889800957824669/25000000000000000000 : ℝ)=(12521889800957824669/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16608368239875424623/16610000000000000000 : ℝ)*(X 1 0+X 2 0)+(164879283807/166100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (4959/100000 : ℝ)) (hi := (2323/10000 : ℝ)) (c := (16608368239875424623/16610000000000000000 : ℝ)) (alpha := (164879283807/166100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16608368239875424623/16610000000000000000 : ℝ)*(X 0 1+X 2 1)+(164879283807/166100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (4959/100000 : ℝ)) (hi := (2323/10000 : ℝ)) (c := (16608368239875424623/16610000000000000000 : ℝ)) (alpha := (164879283807/166100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16608368239875424623/16610000000000000000 : ℝ)*(X 0 2+X 1 2)+(164879283807/166100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (4959/100000 : ℝ)) (hi := (2323/10000 : ℝ)) (c := (16608368239875424623/16610000000000000000 : ℝ)) (alpha := (164879283807/166100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-158561041/1000000000 : ℝ)*X 0 0+(5491840833/10000000000 : ℝ)*X 0 1+(5144403651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5359072267/10000000000 : ℝ)*X 1 0+(-883048523/5000000000 : ℝ)*X 1 1+(128610087/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5359071719/10000000000 : ℝ)*X 2 0+(2572202033/5000000000 : ℝ)*X 2 1+(-883048503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2084599339/5000000000 : ℝ)*X 0 0+(1866995137/5000000000 : ℝ)*X 0 1+(1159923911/2500000000 : ℝ)*X 0 2+(2084599339/5000000000 : ℝ)*X 1 0+(1866995137/5000000000 : ℝ)*X 1 1+(1159923911/2500000000 : ℝ)*X 1 2+(2084599339/5000000000 : ℝ)*X 2 0+(1866995137/5000000000 : ℝ)*X 2 1+(1159923911/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-396439697/2500000000 : ℝ)*X 0 0+(64348707/125000000 : ℝ)*X 0 1+(686037401/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266120069/10000000000 : ℝ)*X 1 0+(-1422201489/10000000000 : ℝ)*X 1 1+(2744149627/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2633059923/5000000000 : ℝ)*X 2 0+(171509361/312500000 : ℝ)*X 2 1+(-711100689/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4169585809/10000000000 : ℝ)*X 0 0+(46305907/100000000 : ℝ)*X 0 1+(1871611457/5000000000 : ℝ)*X 0 2+(4169585809/10000000000 : ℝ)*X 1 0+(46305907/100000000 : ℝ)*X 1 1+(1871611457/5000000000 : ℝ)*X 1 2+(4169585809/10000000000 : ℝ)*X 2 0+(46305907/100000000 : ℝ)*X 2 1+(1871611457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3860777837172340516538087847/415250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2180750263/100000000000000 : ℝ)*(base19) + (895547833/50000000000000 : ℝ)*(base23) + (32225031/10000000000000 : ℝ)*(upper3) + (51090187/100000000000000 : ℝ)*(upper4) + (59079529/25000000000000 : ℝ)*(upper5) + (995596980913679/50000000000000 : ℝ)*(major0) + (995596980913679/50000000000000 : ℝ)*(major1) + (995596980913679/50000000000000 : ℝ)*(major2) + (2878239607392817/100000000000000 : ℝ)*(sp0) + (1439128707864327/50000000000000 : ℝ)*(sp1) + (719564451345813/25000000000000 : ℝ)*(sp2) + (552059836830223/50000000000000 : ℝ)*(sp3) + (199890861/1000000000000 : ℝ)*(sp4) + (8343599401/100000000000000 : ℝ)*(sp7) + (138016002157481/12500000000000 : ℝ)*(f.failure) + (1439129798239459/50000000000000 : ℝ)*(f.sum) + (5694328472671/8305000000000000000000000000 : ℝ)*base65 + (7578103597546918017/830500000000000000000000000000000 : ℝ)*base67 + (6865559562376918017/830500000000000000000000000000000 : ℝ)*base69 + (9480576497071918017/830500000000000000000000000000000 : ℝ)*base71 + (3448455400903/4152500000000000000000000000 : ℝ)*base73 + (7917361026260418017/830500000000000000000000000000000 : ℝ)*base75 + (7403652488186918017/830500000000000000000000000000000 : ℝ)*base77 + (3033781943581418017/830500000000000000000000000000000 : ℝ)*base79 + (345080350391/129765625000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (198683/62500000000000000000 : ℝ)*base89 + (198683/62500000000000000000 : ℝ)*base91 + (198683/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2067574245651262404074425383/415250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1031117559/100000000000000 : ℝ)*(base19) + (100928923/10000000000000 : ℝ)*(base23) + (19033749/50000000000000 : ℝ)*(upper2) + (70015769/50000000000000 : ℝ)*(upper3) + (22886419/20000000000000 : ℝ)*(upper5) + (2032312371600707/100000000000000 : ℝ)*(major0) + (2032312371600707/100000000000000 : ℝ)*(major1) + (2032312371600707/100000000000000 : ℝ)*(major2) + (9848659821/100000000000000 : ℝ)*(sp1) + (2891106389/25000000000000 : ℝ)*(sp2) + (1468848087657271/50000000000000 : ℝ)*(sp4) + (1468842647768581/50000000000000 : ℝ)*(sp5) + (734420900399939/25000000000000 : ℝ)*(sp6) + (112692840191663/10000000000000 : ℝ)*(sp7) + (112692840191663/10000000000000 : ℝ)*(f.failure) + (1468848087657271/50000000000000 : ℝ)*(f.sum) + (40060501644479/8305000000000000000000000000 : ℝ)*base65 + (2678493296733091539/1661000000000000000000000000000000 : ℝ)*base68 + (389330457470908461/1661000000000000000000000000000000 : ℝ)*base69 + (5212806460368091539/1661000000000000000000000000000000 : ℝ)*base72 + (39506479728669/8305000000000000000000000000 : ℝ)*base73 + (19896415190741091539/1661000000000000000000000000000000 : ℝ)*base76 + (693258605623091539/1661000000000000000000000000000000 : ℝ)*base78 + (4171806191301091539/1661000000000000000000000000000000 : ℝ)*base80 + (46902973355169/8305000000000000000000000000 : ℝ)*base81 + (12509/50000000000000000000 : ℝ)*base89 + (12509/50000000000000000000 : ℝ)*base91 + (12509/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1656_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2323/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4959/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9837/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8611/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1656_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1656_s2_0 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-398589721/2500000000 : ℝ)*x 0 + (85140201/156250000 : ℝ)*x 1 + (518149343/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398589721/2500000000 : ℝ)^4943 ≤ (123349929017/1250000000000 : ℝ)^3919 := by
    have hnat : (398589721 : ℕ)^4943*1250000000000^3919 ≤ 123349929017^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398589721 2500000000 123349929017 1250000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85140201/156250000 : ℝ)^4943 ≤ (46496043254079/100000000000000 : ℝ)^3919 := by
    have hnat : (85140201 : ℕ)^4943*100000000000000^3919 ≤ 46496043254079^3919*156250000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85140201 156250000 46496043254079 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518149343/1000000000 : ℝ)^4943 ≤ (21817981208363/50000000000000 : ℝ)^3919 := by
    have hnat : (518149343 : ℕ)^4943*50000000000000^3919 ≤ 21817981208363^3919*1000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518149343 1000000000 21817981208363 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398589721/2500000000 : ℝ), (85140201/156250000 : ℝ), (518149343/1000000000 : ℝ)] ![(123349929017/1250000000000 : ℝ), (46496043254079/100000000000000 : ℝ), (21817981208363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398589721/2500000000 : ℝ)|^4943 ≤ (123349929017/1250000000000 : ℝ)^3919
        have hw : |(-398589721/2500000000 : ℝ)|=(398589721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85140201/156250000 : ℝ)|^4943 ≤ (46496043254079/100000000000000 : ℝ)^3919
        have hw : |(85140201/156250000 : ℝ)|=(85140201/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518149343/1000000000 : ℝ)|^4943 ≤ (21817981208363/50000000000000 : ℝ)^3919
        have hw : |(518149343/1000000000 : ℝ)|=(518149343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s2_1 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673851519/5000000000 : ℝ)*x 0 + (-433027861/2500000000 : ℝ)*x 1 + (323843383/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673851519/5000000000 : ℝ)^4943 ≤ (45408776500767/100000000000000 : ℝ)^3919 := by
    have hnat : (2673851519 : ℕ)^4943*100000000000000^3919 ≤ 45408776500767^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673851519 5000000000 45408776500767 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433027861/2500000000 : ℝ)^4943 ≤ (2191050731309/20000000000000 : ℝ)^3919 := by
    have hnat : (433027861 : ℕ)^4943*20000000000000^3919 ≤ 2191050731309^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433027861 2500000000 2191050731309 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323843383/625000000 : ℝ)^4943 ≤ (43635969830859/100000000000000 : ℝ)^3919 := by
    have hnat : (323843383 : ℕ)^4943*100000000000000^3919 ≤ 43635969830859^3919*625000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323843383 625000000 43635969830859 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673851519/5000000000 : ℝ), (-433027861/2500000000 : ℝ), (323843383/625000000 : ℝ)] ![(45408776500767/100000000000000 : ℝ), (2191050731309/20000000000000 : ℝ), (43635969830859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673851519/5000000000 : ℝ)|^4943 ≤ (45408776500767/100000000000000 : ℝ)^3919
        have hw : |(2673851519/5000000000 : ℝ)|=(2673851519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433027861/2500000000 : ℝ)|^4943 ≤ (2191050731309/20000000000000 : ℝ)^3919
        have hw : |(-433027861/2500000000 : ℝ)|=(433027861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323843383/625000000 : ℝ)|^4943 ≤ (43635969830859/100000000000000 : ℝ)^3919
        have hw : |(323843383/625000000 : ℝ)|=(323843383/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s2_2 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347703479/10000000000 : ℝ)*x 0 + (161921673/312500000 : ℝ)*x 1 + (-1732111639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347703479/10000000000 : ℝ)^4943 ≤ (2270439061193/5000000000000 : ℝ)^3919 := by
    have hnat : (5347703479 : ℕ)^4943*5000000000000^3919 ≤ 2270439061193^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347703479 10000000000 2270439061193 5000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161921673/312500000 : ℝ)^4943 ≤ (21817981771327/50000000000000 : ℝ)^3919 := by
    have hnat : (161921673 : ℕ)^4943*50000000000000^3919 ≤ 21817981771327^3919*312500000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161921673 312500000 21817981771327 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1732111639/10000000000 : ℝ)^4943 ≤ (547762760607/5000000000000 : ℝ)^3919 := by
    have hnat : (1732111639 : ℕ)^4943*5000000000000^3919 ≤ 547762760607^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732111639 10000000000 547762760607 5000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347703479/10000000000 : ℝ), (161921673/312500000 : ℝ), (-1732111639/10000000000 : ℝ)] ![(2270439061193/5000000000000 : ℝ), (21817981771327/50000000000000 : ℝ), (547762760607/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347703479/10000000000 : ℝ)|^4943 ≤ (2270439061193/5000000000000 : ℝ)^3919
        have hw : |(5347703479/10000000000 : ℝ)|=(5347703479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161921673/312500000 : ℝ)|^4943 ≤ (21817981771327/50000000000000 : ℝ)^3919
        have hw : |(161921673/312500000 : ℝ)|=(161921673/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1732111639/10000000000 : ℝ)|^4943 ≤ (547762760607/5000000000000 : ℝ)^3919
        have hw : |(-1732111639/10000000000 : ℝ)|=(1732111639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s2_3 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (104393237/250000000 : ℝ)*x 0 + (3837557751/10000000000 : ℝ)*x 1 + (4534825687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104393237/250000000 : ℝ)^4943 ≤ (8309465460613/25000000000000 : ℝ)^3919 := by
    have hnat : (104393237 : ℕ)^4943*25000000000000^3919 ≤ 8309465460613^3919*250000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104393237 250000000 8309465460613 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3837557751/10000000000 : ℝ)^4943 ≤ (29879419710831/100000000000000 : ℝ)^3919 := by
    have hnat : (3837557751 : ℕ)^4943*100000000000000^3919 ≤ 29879419710831^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3837557751 10000000000 29879419710831 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4534825687/10000000000 : ℝ)^4943 ≤ (2305169902097/6250000000000 : ℝ)^3919 := by
    have hnat : (4534825687 : ℕ)^4943*6250000000000^3919 ≤ 2305169902097^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534825687 10000000000 2305169902097 6250000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104393237/250000000 : ℝ), (3837557751/10000000000 : ℝ), (4534825687/10000000000 : ℝ)] ![(8309465460613/25000000000000 : ℝ), (29879419710831/100000000000000 : ℝ), (2305169902097/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104393237/250000000 : ℝ)|^4943 ≤ (8309465460613/25000000000000 : ℝ)^3919
        have hw : |(104393237/250000000 : ℝ)|=(104393237/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3837557751/10000000000 : ℝ)|^4943 ≤ (29879419710831/100000000000000 : ℝ)^3919
        have hw : |(3837557751/10000000000 : ℝ)|=(3837557751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4534825687/10000000000 : ℝ)|^4943 ≤ (2305169902097/6250000000000 : ℝ)^3919
        have hw : |(4534825687/10000000000 : ℝ)|=(4534825687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s2_4 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-797213299/5000000000 : ℝ)*x 0 + (5183569403/10000000000 : ℝ)*x 1 + (2723437343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (797213299/5000000000 : ℝ)^4943 ≤ (986852293581/10000000000000 : ℝ)^3919 := by
    have hnat : (797213299 : ℕ)^4943*10000000000000^3919 ≤ 986852293581^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797213299 5000000000 986852293581 10000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183569403/10000000000 : ℝ)^4943 ≤ (43658014487853/100000000000000 : ℝ)^3919 := by
    have hnat : (5183569403 : ℕ)^4943*100000000000000^3919 ≤ 43658014487853^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183569403 10000000000 43658014487853 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723437343/5000000000 : ℝ)^4943 ≤ (46473462565713/100000000000000 : ℝ)^3919 := by
    have hnat : (2723437343 : ℕ)^4943*100000000000000^3919 ≤ 46473462565713^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723437343 5000000000 46473462565713 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-797213299/5000000000 : ℝ), (5183569403/10000000000 : ℝ), (2723437343/5000000000 : ℝ)] ![(986852293581/10000000000000 : ℝ), (43658014487853/100000000000000 : ℝ), (46473462565713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-797213299/5000000000 : ℝ)|^4943 ≤ (986852293581/10000000000000 : ℝ)^3919
        have hw : |(-797213299/5000000000 : ℝ)|=(797213299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183569403/10000000000 : ℝ)|^4943 ≤ (43658014487853/100000000000000 : ℝ)^3919
        have hw : |(5183569403/10000000000 : ℝ)|=(5183569403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723437343/5000000000 : ℝ)|^4943 ≤ (46473462565713/100000000000000 : ℝ)^3919
        have hw : |(2723437343/5000000000 : ℝ)|=(2723437343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s2_5 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276192687/10000000000 : ℝ)*x 0 + (-1466730261/10000000000 : ℝ)*x 1 + (85107419/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276192687/10000000000 : ℝ)^4943 ≤ (22322122947951/50000000000000 : ℝ)^3919 := by
    have hnat : (5276192687 : ℕ)^4943*50000000000000^3919 ≤ 22322122947951^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276192687 10000000000 22322122947951 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1466730261/10000000000 : ℝ)^4943 ≤ (8882290125119/100000000000000 : ℝ)^3919 := by
    have hnat : (1466730261 : ℕ)^4943*100000000000000^3919 ≤ 8882290125119^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1466730261 10000000000 8882290125119 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85107419/156250000 : ℝ)^4943 ≤ (46473463964709/100000000000000 : ℝ)^3919 := by
    have hnat : (85107419 : ℕ)^4943*100000000000000^3919 ≤ 46473463964709^3919*156250000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85107419 156250000 46473463964709 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276192687/10000000000 : ℝ), (-1466730261/10000000000 : ℝ), (85107419/156250000 : ℝ)] ![(22322122947951/50000000000000 : ℝ), (8882290125119/100000000000000 : ℝ), (46473463964709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276192687/10000000000 : ℝ)|^4943 ≤ (22322122947951/50000000000000 : ℝ)^3919
        have hw : |(5276192687/10000000000 : ℝ)|=(5276192687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1466730261/10000000000 : ℝ)|^4943 ≤ (8882290125119/100000000000000 : ℝ)^3919
        have hw : |(-1466730261/10000000000 : ℝ)|=(1466730261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85107419/156250000 : ℝ)|^4943 ≤ (46473463964709/100000000000000 : ℝ)^3919
        have hw : |(85107419/156250000 : ℝ)|=(85107419/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s2_6 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329762059/625000000 : ℝ)*x 0 + (5446874441/10000000000 : ℝ)*x 1 + (-1466730431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329762059/625000000 : ℝ)^4943 ≤ (44644248638697/100000000000000 : ℝ)^3919 := by
    have hnat : (329762059 : ℕ)^4943*100000000000000^3919 ≤ 44644248638697^3919*625000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329762059 625000000 44644248638697 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446874441/10000000000 : ℝ)^4943 ≤ (9294691985829/20000000000000 : ℝ)^3919 := by
    have hnat : (5446874441 : ℕ)^4943*20000000000000^3919 ≤ 9294691985829^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446874441 10000000000 9294691985829 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1466730431/10000000000 : ℝ)^4943 ≤ (888229142361/10000000000000 : ℝ)^3919 := by
    have hnat : (1466730431 : ℕ)^4943*10000000000000^3919 ≤ 888229142361^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1466730431 10000000000 888229142361 10000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329762059/625000000 : ℝ), (5446874441/10000000000 : ℝ), (-1466730431/10000000000 : ℝ)] ![(44644248638697/100000000000000 : ℝ), (9294691985829/20000000000000 : ℝ), (888229142361/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329762059/625000000 : ℝ)|^4943 ≤ (44644248638697/100000000000000 : ℝ)^3919
        have hw : |(329762059/625000000 : ℝ)|=(329762059/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446874441/10000000000 : ℝ)|^4943 ≤ (9294691985829/20000000000000 : ℝ)^3919
        have hw : |(5446874441/10000000000 : ℝ)|=(5446874441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1466730431/10000000000 : ℝ)|^4943 ≤ (888229142361/10000000000000 : ℝ)^3919
        have hw : |(-1466730431/10000000000 : ℝ)|=(1466730431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s2_7 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (835181391/2000000000 : ℝ)*x 0 + (2264707677/5000000000 : ℝ)*x 1 + (1921512993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835181391/2000000000 : ℝ)^4943 ≤ (33239643628959/100000000000000 : ℝ)^3919 := by
    have hnat : (835181391 : ℕ)^4943*100000000000000^3919 ≤ 33239643628959^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835181391 2000000000 33239643628959 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264707677/5000000000 : ℝ)^4943 ≤ (36827225977029/100000000000000 : ℝ)^3919 := by
    have hnat : (2264707677 : ℕ)^4943*100000000000000^3919 ≤ 36827225977029^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264707677 5000000000 36827225977029 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921512993/5000000000 : ℝ)^4943 ≤ (7483282595037/25000000000000 : ℝ)^3919 := by
    have hnat : (1921512993 : ℕ)^4943*25000000000000^3919 ≤ 7483282595037^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921512993 5000000000 7483282595037 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835181391/2000000000 : ℝ), (2264707677/5000000000 : ℝ), (1921512993/5000000000 : ℝ)] ![(33239643628959/100000000000000 : ℝ), (36827225977029/100000000000000 : ℝ), (7483282595037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835181391/2000000000 : ℝ)|^4943 ≤ (33239643628959/100000000000000 : ℝ)^3919
        have hw : |(835181391/2000000000 : ℝ)|=(835181391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264707677/5000000000 : ℝ)|^4943 ≤ (36827225977029/100000000000000 : ℝ)^3919
        have hw : |(2264707677/5000000000 : ℝ)|=(2264707677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1921512993/5000000000 : ℝ)|^4943 ≤ (7483282595037/25000000000000 : ℝ)^3919
        have hw : |(1921512993/5000000000 : ℝ)|=(1921512993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1656_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8611/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9837/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5319/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8163/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8611/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9837/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8611/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9837/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8611/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9837/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8611/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9837/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8611/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9837/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8611/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9837/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9837/100000 : ℝ) ^ (4939/1024 : ℝ) ≤ (693909370761389/50000000000000000000 : ℝ) := by
    have hpowers : (9837/100000 : ℝ)^4939 ≤ (693909370761389/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9837 : ℕ)^4939*50000000000000000000^1024 ≤ 693909370761389^1024*100000^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9837 100000 693909370761389 50000000000000000000 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9837/100000 : ℝ)) (X := (693909370761389/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8611/50000 : ℝ) ^ (4939/1024 : ℝ) ≤ (2584378574717787/12500000000000000000 : ℝ) := by
    have hpowers : (8611/50000 : ℝ)^4939 ≤ (2584378574717787/12500000000000000000 : ℝ)^1024 := by
      have hnat : (8611 : ℕ)^4939*12500000000000000000^1024 ≤ 2584378574717787^1024*50000^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8611 50000 2584378574717787 12500000000000000000 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8611/50000 : ℝ)) (X := (2584378574717787/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000693909370761389/25000000000000000000 : ℝ) ≤ (10000057546497591/10000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (25000693909370761389/25000000000000000000 : ℝ)^1024 ≤ (10000057546497591/10000000000000000 : ℝ)^4939 := by
      have hnat : (25000693909370761389 : ℕ)^1024*10000000000000000^4939 ≤ 10000057546497591^4939*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000693909370761389 25000000000000000000 10000057546497591 10000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000057546497591/10000000000000000 : ℝ)) (X := (25000693909370761389/25000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50011031423669632537/50000000000000000000 : ℝ) ≤ (400018295509533/400000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (50011031423669632537/50000000000000000000 : ℝ)^1024 ≤ (400018295509533/400000000000000 : ℝ)^4939 := by
      have hnat : (50011031423669632537 : ℕ)^1024*400000000000000^4939 ≤ 400018295509533^4939*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011031423669632537 50000000000000000000 400018295509533 400000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400018295509533/400000000000000 : ℝ)) (X := (50011031423669632537/50000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252584378574717787/6250000000000000000 : ℝ) ≤ (10000857228979059/10000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (6252584378574717787/6250000000000000000 : ℝ)^1024 ≤ (10000857228979059/10000000000000000 : ℝ)^4939 := by
      have hnat : (6252584378574717787 : ℕ)^1024*10000000000000000^4939 ≤ 10000857228979059^4939*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252584378574717787 6250000000000000000 10000857228979059 10000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000857228979059/10000000000000000 : ℝ)) (X := (6252584378574717787/6250000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(693909370761389/50000000000000000000 : ℝ) ≤ ((73842558504314508819/73850000000000000000 : ℝ)+2*(199920620367/369250000000000 : ℝ)*(9837/100000 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (73842558504314508819/73850000000000000000 : ℝ)+2*(199920620367/369250000000000 : ℝ)*(9837/100000 : ℝ)=(10000057546497591/10000000000000000 : ℝ) by norm_num, show 1+2*(693909370761389/50000000000000000000 : ℝ)=(25000693909370761389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2584378574717787/12500000000000000000 : ℝ)+(693909370761389/50000000000000000000 : ℝ) ≤ ((73842558504314508819/73850000000000000000 : ℝ)+(199920620367/369250000000000 : ℝ)*((8611/50000 : ℝ)+(9837/100000 : ℝ)))^(4939/1024 : ℝ) := by
    rw [show (73842558504314508819/73850000000000000000 : ℝ)+(199920620367/369250000000000 : ℝ)*((8611/50000 : ℝ)+(9837/100000 : ℝ))=(400018295509533/400000000000000 : ℝ) by norm_num, show 1+(2584378574717787/12500000000000000000 : ℝ)+(693909370761389/50000000000000000000 : ℝ)=(50011031423669632537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2584378574717787/12500000000000000000 : ℝ) ≤ ((73842558504314508819/73850000000000000000 : ℝ)+2*(199920620367/369250000000000 : ℝ)*(8611/50000 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (73842558504314508819/73850000000000000000 : ℝ)+2*(199920620367/369250000000000 : ℝ)*(8611/50000 : ℝ)=(10000857228979059/10000000000000000 : ℝ) by norm_num, show 1+2*(2584378574717787/12500000000000000000 : ℝ)=(6252584378574717787/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (73842558504314508819/73850000000000000000 : ℝ)*(X 1 0+X 2 0)+(199920620367/369250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (9837/100000 : ℝ)) (hi := (8611/50000 : ℝ)) (c := (73842558504314508819/73850000000000000000 : ℝ)) (alpha := (199920620367/369250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (73842558504314508819/73850000000000000000 : ℝ)*(X 0 1+X 2 1)+(199920620367/369250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (9837/100000 : ℝ)) (hi := (8611/50000 : ℝ)) (c := (73842558504314508819/73850000000000000000 : ℝ)) (alpha := (199920620367/369250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (73842558504314508819/73850000000000000000 : ℝ)*(X 0 2+X 1 2)+(199920620367/369250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (9837/100000 : ℝ)) (hi := (8611/50000 : ℝ)) (c := (73842558504314508819/73850000000000000000 : ℝ)) (alpha := (199920620367/369250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-398589721/2500000000 : ℝ)*X 0 0+(85140201/156250000 : ℝ)*X 0 1+(518149343/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673851519/5000000000 : ℝ)*X 1 0+(-433027861/2500000000 : ℝ)*X 1 1+(323843383/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347703479/10000000000 : ℝ)*X 2 0+(161921673/312500000 : ℝ)*X 2 1+(-1732111639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((104393237/250000000 : ℝ)*X 0 0+(3837557751/10000000000 : ℝ)*X 0 1+(4534825687/10000000000 : ℝ)*X 0 2+(104393237/250000000 : ℝ)*X 1 0+(3837557751/10000000000 : ℝ)*X 1 1+(4534825687/10000000000 : ℝ)*X 1 2+(104393237/250000000 : ℝ)*X 2 0+(3837557751/10000000000 : ℝ)*X 2 1+(4534825687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-797213299/5000000000 : ℝ)*X 0 0+(5183569403/10000000000 : ℝ)*X 0 1+(2723437343/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276192687/10000000000 : ℝ)*X 1 0+(-1466730261/10000000000 : ℝ)*X 1 1+(85107419/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329762059/625000000 : ℝ)*X 2 0+(5446874441/10000000000 : ℝ)*X 2 1+(-1466730431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((835181391/2000000000 : ℝ)*X 0 0+(2264707677/5000000000 : ℝ)*X 0 1+(1921512993/5000000000 : ℝ)*X 0 2+(835181391/2000000000 : ℝ)*X 1 0+(2264707677/5000000000 : ℝ)*X 1 1+(1921512993/5000000000 : ℝ)*X 1 2+(835181391/2000000000 : ℝ)*X 2 0+(2264707677/5000000000 : ℝ)*X 2 1+(1921512993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1517977167613418413782533007/131875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1394387687/100000000000000 : ℝ)*(base19) + (1592594971/100000000000000 : ℝ)*(base23) + (339472653/100000000000000 : ℝ)*(upper3) + (29439553/50000000000000 : ℝ)*(upper4) + (9570407/6250000000000 : ℝ)*(upper5) + (646604366764057/25000000000000 : ℝ)*(major0) + (646604366764057/25000000000000 : ℝ)*(major1) + (646604366764057/25000000000000 : ℝ)*(major2) + (934657365605151/25000000000000 : ℝ)*(sp0) + (1869325213626119/50000000000000 : ℝ)*(sp1) + (1869325114522477/50000000000000 : ℝ)*(sp2) + (1434174700141801/100000000000000 : ℝ)*(sp3) + (22359219321/100000000000000 : ℝ)*(sp4) + (2007159953/25000000000000 : ℝ)*(sp7) + (1434182728781613/100000000000000 : ℝ)*(f.failure) + (934662955409981/25000000000000 : ℝ)*(f.sum) + (50383092896401/18462500000000000000000000000 : ℝ)*base65 + (4736145711720018683/1846250000000000000000000000000000 : ℝ)*base67 + (8660961790878731317/1846250000000000000000000000000000 : ℝ)*base70 + (15924382792507481317/1846250000000000000000000000000000 : ℝ)*base72 + (254596796241877/36925000000000000000000000000 : ℝ)*base73 + (5052579733338768683/1846250000000000000000000000000000 : ℝ)*base75 + (8923949138499981317/1846250000000000000000000000000000 : ℝ)*base78 + (18068535124061231317/1846250000000000000000000000000000 : ℝ)*base80 + (23111534708827/36925000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2030359/500000000000000000000 : ℝ)*base89 + (2030359/500000000000000000000 : ℝ)*base91 + (2030359/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11109339367588344791382532329/1846250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (457585927/50000000000000 : ℝ)*(base19) + (1200171653/100000000000000 : ℝ)*(base23) + (19646511/12500000000000 : ℝ)*(upper3) + (24728419/50000000000000 : ℝ)*(lower4) + (19709313/25000000000000 : ℝ)*(upper5) + (1313692682912699/50000000000000 : ℝ)*(major0) + (1313692682912699/50000000000000 : ℝ)*(major1) + (1313692682912699/50000000000000 : ℝ)*(major2) + (1454935541/12500000000000 : ℝ)*(sp1) + (12102224977/100000000000000 : ℝ)*(sp2) + (189893543840911/5000000000000 : ℝ)*(sp4) + (1898929161081019/50000000000000 : ℝ)*(sp5) + (379785757442159/10000000000000 : ℝ)*(sp6) + (36422491356443/2500000000000 : ℝ)*(sp7) + (36422491356443/2500000000000 : ℝ)*(f.failure) + (189893543840911/5000000000000 : ℝ)*(f.sum) + (8547403522467/9231250000000000000000000000 : ℝ)*base66 + (28947982252900807519/3692500000000000000000000000000000 : ℝ)*base68 + (68518788848150807519/3692500000000000000000000000000000 : ℝ)*base70 + (25852528596675807519/3692500000000000000000000000000000 : ℝ)*base72 + (41207473250941/18462500000000000000000000000 : ℝ)*base73 + (35994813399010807519/3692500000000000000000000000000000 : ℝ)*base76 + (43056814291478307519/3692500000000000000000000000000000 : ℝ)*base78 + (52166079596285807519/3692500000000000000000000000000000 : ℝ)*base80 + (146259658287343/36925000000000000000000000000 : ℝ)*base82 + (108049/12500000000000000000 : ℝ)*base89 + (108049/12500000000000000000 : ℝ)*base91 + (108049/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1656_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8611/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9837/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1656_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1656_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1656_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1656_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1656_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1656_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
