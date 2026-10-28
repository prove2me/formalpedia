-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1274_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:33.083021+00:00
-- url     : https://prove2.me/submissions/2c3b38d9-2be8-4c7e-ae42-69bbe8c2ca00

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
theorem support_rectangle_w1274_s6_0 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2104848757/10000000000 : ℝ)*x 0 + (2695369181/5000000000 : ℝ)*x 1 + (32921821/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104848757/10000000000 : ℝ)^2117 ≤ (12803427673399/100000000000000 : ℝ)^1605 := by
    have hnat : (2104848757 : ℕ)^2117*100000000000000^1605 ≤ 12803427673399^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104848757 10000000000 12803427673399 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695369181/5000000000 : ℝ)^2117 ≤ (22131620539003/50000000000000 : ℝ)^1605 := by
    have hnat : (2695369181 : ℕ)^2117*50000000000000^1605 ≤ 22131620539003^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695369181 5000000000 22131620539003 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32921821/62500000 : ℝ)^2117 ≤ (2683333201933/6250000000000 : ℝ)^1605 := by
    have hnat : (32921821 : ℕ)^2117*6250000000000^1605 ≤ 2683333201933^1605*62500000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32921821 62500000 2683333201933 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2104848757/10000000000 : ℝ), (2695369181/5000000000 : ℝ), (32921821/62500000 : ℝ)] ![(12803427673399/100000000000000 : ℝ), (22131620539003/50000000000000 : ℝ), (2683333201933/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2104848757/10000000000 : ℝ)|^2117 ≤ (12803427673399/100000000000000 : ℝ)^1605
        have hw : |(-2104848757/10000000000 : ℝ)|=(2104848757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695369181/5000000000 : ℝ)|^2117 ≤ (22131620539003/50000000000000 : ℝ)^1605
        have hw : |(2695369181/5000000000 : ℝ)|=(2695369181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32921821/62500000 : ℝ)|^2117 ≤ (2683333201933/6250000000000 : ℝ)^1605
        have hw : |(32921821/62500000 : ℝ)|=(32921821/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s6_1 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344167181/10000000000 : ℝ)*x 0 + (-2167332773/10000000000 : ℝ)*x 1 + (5267491361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344167181/10000000000 : ℝ)^2117 ≤ (43759557257221/100000000000000 : ℝ)^1605 := by
    have hnat : (5344167181 : ℕ)^2117*100000000000000^1605 ≤ 43759557257221^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344167181 10000000000 43759557257221 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2167332773/10000000000 : ℝ)^2117 ≤ (51980904221/390625000000 : ℝ)^1605 := by
    have hnat : (2167332773 : ℕ)^2117*390625000000^1605 ≤ 51980904221^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167332773 10000000000 51980904221 390625000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267491361/10000000000 : ℝ)^2117 ≤ (21466665620839/50000000000000 : ℝ)^1605 := by
    have hnat : (5267491361 : ℕ)^2117*50000000000000^1605 ≤ 21466665620839^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267491361 10000000000 21466665620839 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344167181/10000000000 : ℝ), (-2167332773/10000000000 : ℝ), (5267491361/10000000000 : ℝ)] ![(43759557257221/100000000000000 : ℝ), (51980904221/390625000000 : ℝ), (21466665620839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344167181/10000000000 : ℝ)|^2117 ≤ (43759557257221/100000000000000 : ℝ)^1605
        have hw : |(5344167181/10000000000 : ℝ)|=(5344167181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2167332773/10000000000 : ℝ)|^2117 ≤ (51980904221/390625000000 : ℝ)^1605
        have hw : |(-2167332773/10000000000 : ℝ)|=(2167332773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267491361/10000000000 : ℝ)|^2117 ≤ (21466665620839/50000000000000 : ℝ)^1605
        have hw : |(5267491361/10000000000 : ℝ)|=(5267491361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s6_2 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068833449/2000000000 : ℝ)*x 0 + (5267491441/10000000000 : ℝ)*x 1 + (-2167332583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068833449/2000000000 : ℝ)^2117 ≤ (8751911589689/20000000000000 : ℝ)^1605 := by
    have hnat : (1068833449 : ℕ)^2117*20000000000000^1605 ≤ 8751911589689^1605*2000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068833449 2000000000 8751911589689 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267491441/10000000000 : ℝ)^2117 ≤ (21466666050867/50000000000000 : ℝ)^1605 := by
    have hnat : (5267491441 : ℕ)^2117*50000000000000^1605 ≤ 21466666050867^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267491441 10000000000 21466666050867 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2167332583/10000000000 : ℝ)^2117 ≤ (13307109941863/100000000000000 : ℝ)^1605 := by
    have hnat : (2167332583 : ℕ)^2117*100000000000000^1605 ≤ 13307109941863^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167332583 10000000000 13307109941863 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068833449/2000000000 : ℝ), (5267491441/10000000000 : ℝ), (-2167332583/10000000000 : ℝ)] ![(8751911589689/20000000000000 : ℝ), (21466666050867/50000000000000 : ℝ), (13307109941863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068833449/2000000000 : ℝ)|^2117 ≤ (8751911589689/20000000000000 : ℝ)^1605
        have hw : |(1068833449/2000000000 : ℝ)|=(1068833449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267491441/10000000000 : ℝ)|^2117 ≤ (21466666050867/50000000000000 : ℝ)^1605
        have hw : |(5267491441/10000000000 : ℝ)|=(5267491441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2167332583/10000000000 : ℝ)|^2117 ≤ (13307109941863/100000000000000 : ℝ)^1605
        have hw : |(-2167332583/10000000000 : ℝ)|=(2167332583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s6_3 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4346259157/10000000000 : ℝ)*x 0 + (4222211961/10000000000 : ℝ)*x 1 + (89476409/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346259157/10000000000 : ℝ)^2117 ≤ (520587096997/1562500000000 : ℝ)^1605 := by
    have hnat : (4346259157 : ℕ)^2117*1562500000000^1605 ≤ 520587096997^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346259157 10000000000 520587096997 1562500000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222211961/10000000000 : ℝ)^2117 ≤ (32069052992613/100000000000000 : ℝ)^1605 := by
    have hnat : (4222211961 : ℕ)^2117*100000000000000^1605 ≤ 32069052992613^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222211961 10000000000 32069052992613 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89476409/200000000 : ℝ)^2117 ≤ (34613372781677/100000000000000 : ℝ)^1605 := by
    have hnat : (89476409 : ℕ)^2117*100000000000000^1605 ≤ 34613372781677^1605*200000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89476409 200000000 34613372781677 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346259157/10000000000 : ℝ), (4222211961/10000000000 : ℝ), (89476409/200000000 : ℝ)] ![(520587096997/1562500000000 : ℝ), (32069052992613/100000000000000 : ℝ), (34613372781677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346259157/10000000000 : ℝ)|^2117 ≤ (520587096997/1562500000000 : ℝ)^1605
        have hw : |(4346259157/10000000000 : ℝ)|=(4346259157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222211961/10000000000 : ℝ)|^2117 ≤ (32069052992613/100000000000000 : ℝ)^1605
        have hw : |(4222211961/10000000000 : ℝ)|=(4222211961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89476409/200000000 : ℝ)|^2117 ≤ (34613372781677/100000000000000 : ℝ)^1605
        have hw : |(89476409/200000000 : ℝ)|=(89476409/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s6_4 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2104853297/10000000000 : ℝ)*x 0 + (2633901743/5000000000 : ℝ)*x 1 + (5390425161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104853297/10000000000 : ℝ)^2117 ≤ (12803464099039/100000000000000 : ℝ)^1605 := by
    have hnat : (2104853297 : ℕ)^2117*100000000000000^1605 ≤ 12803464099039^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104853297 10000000000 12803464099039 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633901743/5000000000 : ℝ)^2117 ≤ (42936686834343/100000000000000 : ℝ)^1605 := by
    have hnat : (2633901743 : ℕ)^2117*100000000000000^1605 ≤ 42936686834343^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633901743 5000000000 42936686834343 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390425161/10000000000 : ℝ)^2117 ≤ (44259849046373/100000000000000 : ℝ)^1605 := by
    have hnat : (5390425161 : ℕ)^2117*100000000000000^1605 ≤ 44259849046373^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390425161 10000000000 44259849046373 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2104853297/10000000000 : ℝ), (2633901743/5000000000 : ℝ), (5390425161/10000000000 : ℝ)] ![(12803464099039/100000000000000 : ℝ), (42936686834343/100000000000000 : ℝ), (44259849046373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2104853297/10000000000 : ℝ)|^2117 ≤ (12803464099039/100000000000000 : ℝ)^1605
        have hw : |(-2104853297/10000000000 : ℝ)|=(2104853297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633901743/5000000000 : ℝ)|^2117 ≤ (42936686834343/100000000000000 : ℝ)^1605
        have hw : |(2633901743/5000000000 : ℝ)|=(2633901743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390425161/10000000000 : ℝ)|^2117 ≤ (44259849046373/100000000000000 : ℝ)^1605
        have hw : |(5390425161/10000000000 : ℝ)|=(5390425161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s6_5 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312651007/10000000000 : ℝ)*x 0 + (-2044398943/10000000000 : ℝ)*x 1 + (2695212597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312651007/10000000000 : ℝ)^2117 ≤ (5427436433541/12500000000000 : ℝ)^1605 := by
    have hnat : (5312651007 : ℕ)^2117*12500000000000^1605 ≤ 5427436433541^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312651007 10000000000 5427436433541 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044398943/10000000000 : ℝ)^2117 ≤ (616032955491/5000000000000 : ℝ)^1605 := by
    have hnat : (2044398943 : ℕ)^2117*5000000000000^1605 ≤ 616032955491^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044398943 10000000000 616032955491 5000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695212597/5000000000 : ℝ)^2117 ≤ (44259849403767/100000000000000 : ℝ)^1605 := by
    have hnat : (2695212597 : ℕ)^2117*100000000000000^1605 ≤ 44259849403767^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695212597 5000000000 44259849403767 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312651007/10000000000 : ℝ), (-2044398943/10000000000 : ℝ), (2695212597/5000000000 : ℝ)] ![(5427436433541/12500000000000 : ℝ), (616032955491/5000000000000 : ℝ), (44259849403767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312651007/10000000000 : ℝ)|^2117 ≤ (5427436433541/12500000000000 : ℝ)^1605
        have hw : |(5312651007/10000000000 : ℝ)|=(5312651007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044398943/10000000000 : ℝ)|^2117 ≤ (616032955491/5000000000000 : ℝ)^1605
        have hw : |(-2044398943/10000000000 : ℝ)|=(2044398943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695212597/5000000000 : ℝ)|^2117 ≤ (44259849403767/100000000000000 : ℝ)^1605
        have hw : |(2695212597/5000000000 : ℝ)|=(2695212597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s6_6 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312650999/10000000000 : ℝ)*x 0 + (1078085039/2000000000 : ℝ)*x 1 + (-1022199477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312650999/10000000000 : ℝ)^2117 ≤ (5427436422761/12500000000000 : ℝ)^1605 := by
    have hnat : (5312650999 : ℕ)^2117*12500000000000^1605 ≤ 5427436422761^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312650999 10000000000 5427436422761 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078085039/2000000000 : ℝ)^2117 ≤ (44259849414597/100000000000000 : ℝ)^1605 := by
    have hnat : (1078085039 : ℕ)^2117*100000000000000^1605 ≤ 44259849414597^1605*2000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078085039 2000000000 44259849414597 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022199477/5000000000 : ℝ)^2117 ≤ (616032959863/5000000000000 : ℝ)^1605 := by
    have hnat : (1022199477 : ℕ)^2117*5000000000000^1605 ≤ 616032959863^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022199477 5000000000 616032959863 5000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312650999/10000000000 : ℝ), (1078085039/2000000000 : ℝ), (-1022199477/5000000000 : ℝ)] ![(5427436422761/12500000000000 : ℝ), (44259849414597/100000000000000 : ℝ), (616032959863/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312650999/10000000000 : ℝ)|^2117 ≤ (5427436422761/12500000000000 : ℝ)^1605
        have hw : |(5312650999/10000000000 : ℝ)|=(5312650999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078085039/2000000000 : ℝ)|^2117 ≤ (44259849414597/100000000000000 : ℝ)^1605
        have hw : |(1078085039/2000000000 : ℝ)|=(1078085039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022199477/5000000000 : ℝ)|^2117 ≤ (616032959863/5000000000000 : ℝ)^1605
        have hw : |(-1022199477/5000000000 : ℝ)|=(1022199477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s6_7 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1086567183/2500000000 : ℝ)*x 0 + (4473183637/10000000000 : ℝ)*x 1 + (4222850949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086567183/2500000000 : ℝ)^2117 ≤ (33317671022777/100000000000000 : ℝ)^1605 := by
    have hnat : (1086567183 : ℕ)^2117*100000000000000^1605 ≤ 33317671022777^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086567183 2500000000 33317671022777 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4473183637/10000000000 : ℝ)^2117 ≤ (34606874279771/100000000000000 : ℝ)^1605 := by
    have hnat : (4473183637 : ℕ)^2117*100000000000000^1605 ≤ 34606874279771^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473183637 10000000000 34606874279771 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222850949/10000000000 : ℝ)^2117 ≤ (16037727344773/50000000000000 : ℝ)^1605 := by
    have hnat : (4222850949 : ℕ)^2117*50000000000000^1605 ≤ 16037727344773^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222850949 10000000000 16037727344773 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086567183/2500000000 : ℝ), (4473183637/10000000000 : ℝ), (4222850949/10000000000 : ℝ)] ![(33317671022777/100000000000000 : ℝ), (34606874279771/100000000000000 : ℝ), (16037727344773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086567183/2500000000 : ℝ)|^2117 ≤ (33317671022777/100000000000000 : ℝ)^1605
        have hw : |(1086567183/2500000000 : ℝ)|=(1086567183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4473183637/10000000000 : ℝ)|^2117 ≤ (34606874279771/100000000000000 : ℝ)^1605
        have hw : |(4473183637/10000000000 : ℝ)|=(4473183637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222850949/10000000000 : ℝ)|^2117 ≤ (16037727344773/50000000000000 : ℝ)^1605
        have hw : |(4222850949/10000000000 : ℝ)|=(4222850949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1274_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (442/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5757/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (113/800 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (442/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1437/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (442/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1437/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (442/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1437/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (442/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1437/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (442/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1437/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (442/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1437/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1437/12500 : ℝ) ^ (8467/2048 : ℝ) ≤ (13062903969885517/100000000000000000000 : ℝ) := by
    have hpowers : (1437/12500 : ℝ)^8467 ≤ (13062903969885517/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1437 : ℕ)^8467*100000000000000000000^2048 ≤ 13062903969885517^2048*12500^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1437 12500 13062903969885517 100000000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1437/12500 : ℝ)) (X := (13062903969885517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (442/3125 : ℝ) ^ (8467/2048 : ℝ) ≤ (30777269567316997/100000000000000000000 : ℝ) := by
    have hpowers : (442/3125 : ℝ)^8467 ≤ (30777269567316997/100000000000000000000 : ℝ)^2048 := by
      have hnat : (442 : ℕ)^8467*100000000000000000000^2048 ≤ 30777269567316997^2048*3125^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        442 3125 30777269567316997 100000000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (442/3125 : ℝ)) (X := (30777269567316997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013062903969885517/50000000000000000000 : ℝ) ≤ (2000126373819949/2000000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (50013062903969885517/50000000000000000000 : ℝ)^2048 ≤ (2000126373819949/2000000000000000 : ℝ)^8467 := by
      have hnat : (50013062903969885517 : ℕ)^2048*2000000000000000^8467 ≤ 2000126373819949^8467*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013062903969885517 50000000000000000000 2000126373819949 2000000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000126373819949/2000000000000000 : ℝ)) (X := (50013062903969885517/50000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021920086768601257/50000000000000000000 : ℝ) ≤ (250026505775001/250000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (50021920086768601257/50000000000000000000 : ℝ)^2048 ≤ (250026505775001/250000000000000 : ℝ)^8467 := by
      have hnat : (50021920086768601257 : ℕ)^2048*250000000000000^8467 ≤ 250026505775001^8467*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021920086768601257 50000000000000000000 250026505775001 250000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250026505775001/250000000000000 : ℝ)) (X := (50021920086768601257/50000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030777269567316997/50000000000000000000 : ℝ) ≤ (2000297718580067/2000000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (50030777269567316997/50000000000000000000 : ℝ)^2048 ≤ (2000297718580067/2000000000000000 : ℝ)^8467 := by
      have hnat : (50030777269567316997 : ℕ)^2048*2000000000000000^8467 ≤ 2000297718580067^8467*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030777269567316997 50000000000000000000 2000297718580067 2000000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000297718580067/2000000000000000 : ℝ)) (X := (50030777269567316997/50000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13062903969885517/100000000000000000000 : ℝ) ≤ ((661795607314113553/662000000000000000 : ℝ)+2*(85672380059/52960000000000 : ℝ)*(1437/12500 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (661795607314113553/662000000000000000 : ℝ)+2*(85672380059/52960000000000 : ℝ)*(1437/12500 : ℝ)=(2000126373819949/2000000000000000 : ℝ) by norm_num, show 1+2*(13062903969885517/100000000000000000000 : ℝ)=(50013062903969885517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30777269567316997/100000000000000000000 : ℝ)+(13062903969885517/100000000000000000000 : ℝ) ≤ ((661795607314113553/662000000000000000 : ℝ)+(85672380059/52960000000000 : ℝ)*((442/3125 : ℝ)+(1437/12500 : ℝ)))^(8467/2048 : ℝ) := by
    rw [show (661795607314113553/662000000000000000 : ℝ)+(85672380059/52960000000000 : ℝ)*((442/3125 : ℝ)+(1437/12500 : ℝ))=(250026505775001/250000000000000 : ℝ) by norm_num, show 1+(30777269567316997/100000000000000000000 : ℝ)+(13062903969885517/100000000000000000000 : ℝ)=(50021920086768601257/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30777269567316997/100000000000000000000 : ℝ) ≤ ((661795607314113553/662000000000000000 : ℝ)+2*(85672380059/52960000000000 : ℝ)*(442/3125 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (661795607314113553/662000000000000000 : ℝ)+2*(85672380059/52960000000000 : ℝ)*(442/3125 : ℝ)=(2000297718580067/2000000000000000 : ℝ) by norm_num, show 1+2*(30777269567316997/100000000000000000000 : ℝ)=(50030777269567316997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (661795607314113553/662000000000000000 : ℝ)*(X 1 0+X 2 0)+(85672380059/52960000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (1437/12500 : ℝ)) (hi := (442/3125 : ℝ)) (c := (661795607314113553/662000000000000000 : ℝ)) (alpha := (85672380059/52960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (661795607314113553/662000000000000000 : ℝ)*(X 0 1+X 2 1)+(85672380059/52960000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (1437/12500 : ℝ)) (hi := (442/3125 : ℝ)) (c := (661795607314113553/662000000000000000 : ℝ)) (alpha := (85672380059/52960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (661795607314113553/662000000000000000 : ℝ)*(X 0 2+X 1 2)+(85672380059/52960000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (1437/12500 : ℝ)) (hi := (442/3125 : ℝ)) (c := (661795607314113553/662000000000000000 : ℝ)) (alpha := (85672380059/52960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2104848757/10000000000 : ℝ)*X 0 0+(2695369181/5000000000 : ℝ)*X 0 1+(32921821/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344167181/10000000000 : ℝ)*X 1 0+(-2167332773/10000000000 : ℝ)*X 1 1+(5267491361/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068833449/2000000000 : ℝ)*X 2 0+(5267491441/10000000000 : ℝ)*X 2 1+(-2167332583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4346259157/10000000000 : ℝ)*X 0 0+(4222211961/10000000000 : ℝ)*X 0 1+(89476409/200000000 : ℝ)*X 0 2+(4346259157/10000000000 : ℝ)*X 1 0+(4222211961/10000000000 : ℝ)*X 1 1+(89476409/200000000 : ℝ)*X 1 2+(4346259157/10000000000 : ℝ)*X 2 0+(4222211961/10000000000 : ℝ)*X 2 1+(89476409/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2104853297/10000000000 : ℝ)*X 0 0+(2633901743/5000000000 : ℝ)*X 0 1+(5390425161/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312651007/10000000000 : ℝ)*X 1 0+(-2044398943/10000000000 : ℝ)*X 1 1+(2695212597/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312650999/10000000000 : ℝ)*X 2 0+(1078085039/2000000000 : ℝ)*X 2 1+(-1022199477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1086567183/2500000000 : ℝ)*X 0 0+(4473183637/10000000000 : ℝ)*X 0 1+(4222850949/10000000000 : ℝ)*X 0 2+(1086567183/2500000000 : ℝ)*X 1 0+(4473183637/10000000000 : ℝ)*X 1 1+(4222850949/10000000000 : ℝ)*X 1 2+(1086567183/2500000000 : ℝ)*X 2 0+(4473183637/10000000000 : ℝ)*X 2 1+(4222850949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9839293969487962175397/1324000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1664383777/100000000000000 : ℝ)*(base19) + (1639346479/100000000000000 : ℝ)*(base23) + (19692271/50000000000000 : ℝ)*(upper3) + (65309259/100000000000000 : ℝ)*(upper4) + (142594041/50000000000000 : ℝ)*(upper5) + (3022090523405993/50000000000000 : ℝ)*(major0) + (3022090523405993/50000000000000 : ℝ)*(major1) + (3022090523405993/50000000000000 : ℝ)*(major2) + (202845815378613/2500000000000 : ℝ)*(sp0) + (2028472971456267/25000000000000 : ℝ)*(sp1) + (1622778382172473/20000000000000 : ℝ)*(sp2) + (248403148853079/6250000000000 : ℝ)*(sp3) + (15233766081/25000000000000 : ℝ)*(sp4) + (17914049491/100000000000000 : ℝ)*(sp7) + (993617073924689/25000000000000 : ℝ)*(f.failure) + (2028473387552211/25000000000000 : ℝ)*(f.sum) + (3946847007821/1324000000000000000000000000 : ℝ)*base66 + (300758181500060629/33100000000000000000000000000000 : ℝ)*base67 + (78079062178739371/33100000000000000000000000000000 : ℝ)*base70 + (153277298668239371/33100000000000000000000000000000 : ℝ)*base72 + (6350415311281/1324000000000000000000000000 : ℝ)*base74 + (427377873669139371/33100000000000000000000000000000 : ℝ)*base76 + (71023490359060629/33100000000000000000000000000000 : ℝ)*base77 + (273384208060960629/33100000000000000000000000000000 : ℝ)*base79 + (5136138593251/1324000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (27784379/2500000000000000000000 : ℝ)*base89 + (27784379/2500000000000000000000 : ℝ)*base91 + (27784379/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122981982689980176482928033/33100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (684865661/100000000000000 : ℝ)*(base19) + (368327489/50000000000000 : ℝ)*(base23) + (42683247/50000000000000 : ℝ)*(upper3) + (7624277/25000000000000 : ℝ)*(lower4) + (39874889/50000000000000 : ℝ)*(upper5) + (6074923822902387/100000000000000 : ℝ)*(major0) + (6074923822902387/100000000000000 : ℝ)*(major1) + (6074923822902387/100000000000000 : ℝ)*(major2) + (20925036747/100000000000000 : ℝ)*(sp1) + (22048497513/100000000000000 : ℝ)*(sp2) + (8155163718490731/100000000000000 : ℝ)*(sp4) + (4077571054294161/50000000000000 : ℝ)*(sp5) + (12742407708341/156250000000 : ℝ)*(sp6) + (998670950866277/25000000000000 : ℝ)*(sp7) + (998670950866277/25000000000000 : ℝ)*(f.failure) + (8155163718490731/100000000000000 : ℝ)*(f.sum) + (17610088788119/2648000000000000000000000000 : ℝ)*base66 + (922941555991236489/66200000000000000000000000000000 : ℝ)*base68 + (669696376801436489/66200000000000000000000000000000 : ℝ)*base70 + (763970031512236489/66200000000000000000000000000000 : ℝ)*base72 + (553677164921/2648000000000000000000000000 : ℝ)*base73 + (602313821005763511/66200000000000000000000000000000 : ℝ)*base75 + (108458386946963511/66200000000000000000000000000000 : ℝ)*base77 + (1291659321566636489/66200000000000000000000000000000 : ℝ)*base80 + (6908216658711/2648000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (32559447/2500000000000000000000 : ℝ)*base89 + (32559447/2500000000000000000000 : ℝ)*base91 + (32559447/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1274_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (442/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5757/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (113/800 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1274_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1274_s7_0 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1052431553/5000000000 : ℝ)*x 0 + (5390568897/10000000000 : ℝ)*x 1 + (526765137/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052431553/5000000000 : ℝ)^2117 ≤ (2560708559873/20000000000000 : ℝ)^1605 := by
    have hnat : (1052431553 : ℕ)^2117*20000000000000^1605 ≤ 2560708559873^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052431553 5000000000 2560708559873 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390568897/10000000000 : ℝ)^2117 ≤ (44261405729187/100000000000000 : ℝ)^1605 := by
    have hnat : (5390568897 : ℕ)^2117*100000000000000^1605 ≤ 44261405729187^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390568897 10000000000 44261405729187 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526765137/1000000000 : ℝ)^2117 ≤ (42935051458109/100000000000000 : ℝ)^1605 := by
    have hnat : (526765137 : ℕ)^2117*100000000000000^1605 ≤ 42935051458109^1605*1000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526765137 1000000000 42935051458109 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1052431553/5000000000 : ℝ), (5390568897/10000000000 : ℝ), (526765137/1000000000 : ℝ)] ![(2560708559873/20000000000000 : ℝ), (44261405729187/100000000000000 : ℝ), (42935051458109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1052431553/5000000000 : ℝ)|^2117 ≤ (2560708559873/20000000000000 : ℝ)^1605
        have hw : |(-1052431553/5000000000 : ℝ)|=(1052431553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390568897/10000000000 : ℝ)|^2117 ≤ (44261405729187/100000000000000 : ℝ)^1605
        have hw : |(5390568897/10000000000 : ℝ)|=(5390568897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526765137/1000000000 : ℝ)|^2117 ≤ (42935051458109/100000000000000 : ℝ)^1605
        have hw : |(526765137/1000000000 : ℝ)|=(526765137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s7_1 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344123851/10000000000 : ℝ)*x 0 + (-2167177813/10000000000 : ℝ)*x 1 + (263382581/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344123851/10000000000 : ℝ)^2117 ≤ (21879544638859/50000000000000 : ℝ)^1605 := by
    have hnat : (5344123851 : ℕ)^2117*50000000000000^1605 ≤ 21879544638859^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344123851 10000000000 21879544638859 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2167177813/10000000000 : ℝ)^2117 ≤ (1330585655297/10000000000000 : ℝ)^1605 := by
    have hnat : (2167177813 : ℕ)^2117*10000000000000^1605 ≤ 1330585655297^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167177813 10000000000 1330585655297 10000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263382581/500000000 : ℝ)^2117 ≤ (42935054145809/100000000000000 : ℝ)^1605 := by
    have hnat : (263382581 : ℕ)^2117*100000000000000^1605 ≤ 42935054145809^1605*500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263382581 500000000 42935054145809 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344123851/10000000000 : ℝ), (-2167177813/10000000000 : ℝ), (263382581/500000000 : ℝ)] ![(21879544638859/50000000000000 : ℝ), (1330585655297/10000000000000 : ℝ), (42935054145809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344123851/10000000000 : ℝ)|^2117 ≤ (21879544638859/50000000000000 : ℝ)^1605
        have hw : |(5344123851/10000000000 : ℝ)|=(5344123851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2167177813/10000000000 : ℝ)|^2117 ≤ (1330585655297/10000000000000 : ℝ)^1605
        have hw : |(-2167177813/10000000000 : ℝ)|=(2167177813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263382581/500000000 : ℝ)|^2117 ≤ (42935054145809/100000000000000 : ℝ)^1605
        have hw : |(263382581/500000000 : ℝ)|=(263382581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s7_2 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672061859/5000000000 : ℝ)*x 0 + (5267651653/10000000000 : ℝ)*x 1 + (-2167177947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672061859/5000000000 : ℝ)^2117 ≤ (5469885980159/12500000000000 : ℝ)^1605 := by
    have hnat : (2672061859 : ℕ)^2117*12500000000000^1605 ≤ 5469885980159^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672061859 5000000000 5469885980159 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267651653/10000000000 : ℝ)^2117 ≤ (21467527250293/50000000000000 : ℝ)^1605 := by
    have hnat : (5267651653 : ℕ)^2117*50000000000000^1605 ≤ 21467527250293^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267651653 10000000000 21467527250293 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2167177947/10000000000 : ℝ)^2117 ≤ (13305857638143/100000000000000 : ℝ)^1605 := by
    have hnat : (2167177947 : ℕ)^2117*100000000000000^1605 ≤ 13305857638143^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167177947 10000000000 13305857638143 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672061859/5000000000 : ℝ), (5267651653/10000000000 : ℝ), (-2167177947/10000000000 : ℝ)] ![(5469885980159/12500000000000 : ℝ), (21467527250293/50000000000000 : ℝ), (13305857638143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672061859/5000000000 : ℝ)|^2117 ≤ (5469885980159/12500000000000 : ℝ)^1605
        have hw : |(2672061859/5000000000 : ℝ)|=(2672061859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267651653/10000000000 : ℝ)|^2117 ≤ (21467527250293/50000000000000 : ℝ)^1605
        have hw : |(5267651653/10000000000 : ℝ)|=(5267651653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2167177947/10000000000 : ℝ)|^2117 ≤ (13305857638143/100000000000000 : ℝ)^1605
        have hw : |(-2167177947/10000000000 : ℝ)|=(2167177947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s7_3 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (869253593/2000000000 : ℝ)*x 0 + (422254631/1000000000 : ℝ)*x 1 + (1118370871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869253593/2000000000 : ℝ)^2117 ≤ (16658831633733/50000000000000 : ℝ)^1605 := by
    have hnat : (869253593 : ℕ)^2117*50000000000000^1605 ≤ 16658831633733^1605*2000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869253593 2000000000 16658831633733 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422254631/1000000000 : ℝ)^2117 ≤ (128289610509/400000000000 : ℝ)^1605 := by
    have hnat : (422254631 : ℕ)^2117*400000000000^1605 ≤ 128289610509^1605*1000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422254631 1000000000 128289610509 400000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1118370871/2500000000 : ℝ)^2117 ≤ (17304967049679/50000000000000 : ℝ)^1605 := by
    have hnat : (1118370871 : ℕ)^2117*50000000000000^1605 ≤ 17304967049679^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118370871 2500000000 17304967049679 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869253593/2000000000 : ℝ), (422254631/1000000000 : ℝ), (1118370871/2500000000 : ℝ)] ![(16658831633733/50000000000000 : ℝ), (128289610509/400000000000 : ℝ), (17304967049679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869253593/2000000000 : ℝ)|^2117 ≤ (16658831633733/50000000000000 : ℝ)^1605
        have hw : |(869253593/2000000000 : ℝ)|=(869253593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422254631/1000000000 : ℝ)|^2117 ≤ (128289610509/400000000000 : ℝ)^1605
        have hw : |(422254631/1000000000 : ℝ)|=(422254631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1118370871/2500000000 : ℝ)|^2117 ≤ (17304967049679/50000000000000 : ℝ)^1605
        have hw : |(1118370871/2500000000 : ℝ)|=(1118370871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s7_4 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2104868497/10000000000 : ℝ)*x 0 + (2633980551/5000000000 : ℝ)*x 1 + (1347564359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104868497/10000000000 : ℝ)^2117 ≤ (12803586052903/100000000000000 : ℝ)^1605 := by
    have hnat : (2104868497 : ℕ)^2117*100000000000000^1605 ≤ 12803586052903^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104868497 10000000000 12803586052903 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633980551/5000000000 : ℝ)^2117 ≤ (2146919067807/5000000000000 : ℝ)^1605 := by
    have hnat : (2633980551 : ℕ)^2117*5000000000000^1605 ≤ 2146919067807^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633980551 5000000000 2146919067807 5000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347564359/2500000000 : ℝ)^2117 ≤ (4425803257577/10000000000000 : ℝ)^1605 := by
    have hnat : (1347564359 : ℕ)^2117*10000000000000^1605 ≤ 4425803257577^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347564359 2500000000 4425803257577 10000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2104868497/10000000000 : ℝ), (2633980551/5000000000 : ℝ), (1347564359/2500000000 : ℝ)] ![(12803586052903/100000000000000 : ℝ), (2146919067807/5000000000000 : ℝ), (4425803257577/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2104868497/10000000000 : ℝ)|^2117 ≤ (12803586052903/100000000000000 : ℝ)^1605
        have hw : |(-2104868497/10000000000 : ℝ)|=(2104868497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633980551/5000000000 : ℝ)|^2117 ≤ (2146919067807/5000000000000 : ℝ)^1605
        have hw : |(2633980551/5000000000 : ℝ)|=(2633980551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347564359/2500000000 : ℝ)|^2117 ≤ (4425803257577/10000000000000 : ℝ)^1605
        have hw : |(1347564359/2500000000 : ℝ)|=(1347564359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s7_5 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (132817301/250000000 : ℝ)*x 0 + (-1022286181/5000000000 : ℝ)*x 1 + (5390257063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132817301/250000000 : ℝ)^2117 ≤ (5427491725641/12500000000000 : ℝ)^1605 := by
    have hnat : (132817301 : ℕ)^2117*12500000000000^1605 ≤ 5427491725641^1605*250000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132817301 250000000 5427491725641 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022286181/5000000000 : ℝ)^2117 ≤ (6161018820619/50000000000000 : ℝ)^1605 := by
    have hnat : (1022286181 : ℕ)^2117*50000000000000^1605 ≤ 6161018820619^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022286181 5000000000 6161018820619 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390257063/10000000000 : ℝ)^2117 ≤ (2212901426809/5000000000000 : ℝ)^1605 := by
    have hnat : (5390257063 : ℕ)^2117*5000000000000^1605 ≤ 2212901426809^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390257063 10000000000 2212901426809 5000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132817301/250000000 : ℝ), (-1022286181/5000000000 : ℝ), (5390257063/10000000000 : ℝ)] ![(5427491725641/12500000000000 : ℝ), (6161018820619/50000000000000 : ℝ), (2212901426809/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132817301/250000000 : ℝ)|^2117 ≤ (5427491725641/12500000000000 : ℝ)^1605
        have hw : |(132817301/250000000 : ℝ)|=(132817301/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1022286181/5000000000 : ℝ)|^2117 ≤ (6161018820619/50000000000000 : ℝ)^1605
        have hw : |(-1022286181/5000000000 : ℝ)|=(1022286181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390257063/10000000000 : ℝ)|^2117 ≤ (2212901426809/5000000000000 : ℝ)^1605
        have hw : |(5390257063/10000000000 : ℝ)|=(5390257063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s7_6 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656346299/5000000000 : ℝ)*x 0 + (5390256473/10000000000 : ℝ)*x 1 + (-2044572409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656346299/5000000000 : ℝ)^2117 ≤ (43419939820389/100000000000000 : ℝ)^1605 := by
    have hnat : (2656346299 : ℕ)^2117*100000000000000^1605 ≤ 43419939820389^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656346299 5000000000 43419939820389 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390256473/10000000000 : ℝ)^2117 ≤ (44258022146481/100000000000000 : ℝ)^1605 := by
    have hnat : (5390256473 : ℕ)^2117*100000000000000^1605 ≤ 44258022146481^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390256473 10000000000 44258022146481 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2044572409/10000000000 : ℝ)^2117 ≤ (12322038014853/100000000000000 : ℝ)^1605 := by
    have hnat : (2044572409 : ℕ)^2117*100000000000000^1605 ≤ 12322038014853^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044572409 10000000000 12322038014853 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656346299/5000000000 : ℝ), (5390256473/10000000000 : ℝ), (-2044572409/10000000000 : ℝ)] ![(43419939820389/100000000000000 : ℝ), (44258022146481/100000000000000 : ℝ), (12322038014853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656346299/5000000000 : ℝ)|^2117 ≤ (43419939820389/100000000000000 : ℝ)^1605
        have hw : |(2656346299/5000000000 : ℝ)|=(2656346299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390256473/10000000000 : ℝ)|^2117 ≤ (44258022146481/100000000000000 : ℝ)^1605
        have hw : |(5390256473/10000000000 : ℝ)|=(5390256473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2044572409/10000000000 : ℝ)|^2117 ≤ (12322038014853/100000000000000 : ℝ)^1605
        have hw : |(-2044572409/10000000000 : ℝ)|=(2044572409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s7_7 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2173138381/5000000000 : ℝ)*x 0 + (4472849943/10000000000 : ℝ)*x 1 + (2111591359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173138381/5000000000 : ℝ)^2117 ≤ (16658876107979/50000000000000 : ℝ)^1605 := by
    have hnat : (2173138381 : ℕ)^2117*50000000000000^1605 ≤ 16658876107979^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173138381 5000000000 16658876107979 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4472849943/10000000000 : ℝ)^2117 ≤ (34603469141913/100000000000000 : ℝ)^1605 := by
    have hnat : (4472849943 : ℕ)^2117*100000000000000^1605 ≤ 34603469141913^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472849943 10000000000 34603469141913 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111591359/5000000000 : ℝ)^2117 ≤ (6415755727379/20000000000000 : ℝ)^1605 := by
    have hnat : (2111591359 : ℕ)^2117*20000000000000^1605 ≤ 6415755727379^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111591359 5000000000 6415755727379 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173138381/5000000000 : ℝ), (4472849943/10000000000 : ℝ), (2111591359/5000000000 : ℝ)] ![(16658876107979/50000000000000 : ℝ), (34603469141913/100000000000000 : ℝ), (6415755727379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173138381/5000000000 : ℝ)|^2117 ≤ (16658876107979/50000000000000 : ℝ)^1605
        have hw : |(2173138381/5000000000 : ℝ)|=(2173138381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4472849943/10000000000 : ℝ)|^2117 ≤ (34603469141913/100000000000000 : ℝ)^1605
        have hw : |(4472849943/10000000000 : ℝ)|=(4472849943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111591359/5000000000 : ℝ)|^2117 ≤ (6415755727379/20000000000000 : ℝ)^1605
        have hw : |(2111591359/5000000000 : ℝ)|=(2111591359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1274_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (113/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5757/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5759/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7061/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (113/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5757/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (113/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5757/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (113/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5757/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (113/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5757/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (113/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5757/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (113/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5757/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5757/50000 : ℝ) ^ (8467/2048 : ℝ) ≤ (2629534342898137/20000000000000000000 : ℝ) := by
    have hpowers : (5757/50000 : ℝ)^8467 ≤ (2629534342898137/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5757 : ℕ)^8467*20000000000000000000^2048 ≤ 2629534342898137^2048*50000^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5757 50000 2629534342898137 20000000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5757/50000 : ℝ)) (X := (2629534342898137/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (113/800 : ℝ) ^ (8467/2048 : ℝ) ≤ (30606701906479633/100000000000000000000 : ℝ) := by
    have hpowers : (113/800 : ℝ)^8467 ≤ (30606701906479633/100000000000000000000 : ℝ)^2048 := by
      have hnat : (113 : ℕ)^8467*100000000000000000000^2048 ≤ 30606701906479633^2048*800^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 800 30606701906479633 100000000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/800 : ℝ)) (X := (30606701906479633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002629534342898137/10000000000000000000 : ℝ) ≤ (2000127193802717/2000000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (10002629534342898137/10000000000000000000 : ℝ)^2048 ≤ (2000127193802717/2000000000000000 : ℝ)^8467 := by
      have hnat : (10002629534342898137 : ℕ)^2048*2000000000000000^8467 ≤ 2000127193802717^8467*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002629534342898137 10000000000000000000 2000127193802717 2000000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000127193802717/2000000000000000 : ℝ)) (X := (10002629534342898137/10000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021877186810485159/50000000000000000000 : ℝ) ≤ (5000529078179209/5000000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (50021877186810485159/50000000000000000000 : ℝ)^2048 ≤ (5000529078179209/5000000000000000 : ℝ)^8467 := by
      have hnat : (50021877186810485159 : ℕ)^2048*5000000000000000^8467 ≤ 5000529078179209^8467*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021877186810485159 50000000000000000000 5000529078179209 5000000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000529078179209/5000000000000000 : ℝ)) (X := (50021877186810485159/50000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030606701906479633/50000000000000000000 : ℝ) ≤ (10001480343703251/10000000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (50030606701906479633/50000000000000000000 : ℝ)^2048 ≤ (10001480343703251/10000000000000000 : ℝ)^8467 := by
      have hnat : (50030606701906479633 : ℕ)^2048*10000000000000000^8467 ≤ 10001480343703251^8467*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030606701906479633 50000000000000000000 10001480343703251 10000000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001480343703251/10000000000000000 : ℝ)) (X := (50030606701906479633/50000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2629534342898137/20000000000000000000 : ℝ) ≤ ((26101938384917656111/26110000000000000000 : ℝ)+2*(422187344833/261100000000000 : ℝ)*(5757/50000 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (26101938384917656111/26110000000000000000 : ℝ)+2*(422187344833/261100000000000 : ℝ)*(5757/50000 : ℝ)=(2000127193802717/2000000000000000 : ℝ) by norm_num, show 1+2*(2629534342898137/20000000000000000000 : ℝ)=(10002629534342898137/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30606701906479633/100000000000000000000 : ℝ)+(2629534342898137/20000000000000000000 : ℝ) ≤ ((26101938384917656111/26110000000000000000 : ℝ)+(422187344833/261100000000000 : ℝ)*((113/800 : ℝ)+(5757/50000 : ℝ)))^(8467/2048 : ℝ) := by
    rw [show (26101938384917656111/26110000000000000000 : ℝ)+(422187344833/261100000000000 : ℝ)*((113/800 : ℝ)+(5757/50000 : ℝ))=(5000529078179209/5000000000000000 : ℝ) by norm_num, show 1+(30606701906479633/100000000000000000000 : ℝ)+(2629534342898137/20000000000000000000 : ℝ)=(50021877186810485159/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30606701906479633/100000000000000000000 : ℝ) ≤ ((26101938384917656111/26110000000000000000 : ℝ)+2*(422187344833/261100000000000 : ℝ)*(113/800 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (26101938384917656111/26110000000000000000 : ℝ)+2*(422187344833/261100000000000 : ℝ)*(113/800 : ℝ)=(10001480343703251/10000000000000000 : ℝ) by norm_num, show 1+2*(30606701906479633/100000000000000000000 : ℝ)=(50030606701906479633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26101938384917656111/26110000000000000000 : ℝ)*(X 1 0+X 2 0)+(422187344833/261100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (5757/50000 : ℝ)) (hi := (113/800 : ℝ)) (c := (26101938384917656111/26110000000000000000 : ℝ)) (alpha := (422187344833/261100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26101938384917656111/26110000000000000000 : ℝ)*(X 0 1+X 2 1)+(422187344833/261100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (5757/50000 : ℝ)) (hi := (113/800 : ℝ)) (c := (26101938384917656111/26110000000000000000 : ℝ)) (alpha := (422187344833/261100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26101938384917656111/26110000000000000000 : ℝ)*(X 0 2+X 1 2)+(422187344833/261100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (5757/50000 : ℝ)) (hi := (113/800 : ℝ)) (c := (26101938384917656111/26110000000000000000 : ℝ)) (alpha := (422187344833/261100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1052431553/5000000000 : ℝ)*X 0 0+(5390568897/10000000000 : ℝ)*X 0 1+(526765137/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344123851/10000000000 : ℝ)*X 1 0+(-2167177813/10000000000 : ℝ)*X 1 1+(263382581/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672061859/5000000000 : ℝ)*X 2 0+(5267651653/10000000000 : ℝ)*X 2 1+(-2167177947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869253593/2000000000 : ℝ)*X 0 0+(422254631/1000000000 : ℝ)*X 0 1+(1118370871/2500000000 : ℝ)*X 0 2+(869253593/2000000000 : ℝ)*X 1 0+(422254631/1000000000 : ℝ)*X 1 1+(1118370871/2500000000 : ℝ)*X 1 2+(869253593/2000000000 : ℝ)*X 2 0+(422254631/1000000000 : ℝ)*X 2 1+(1118370871/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2104868497/10000000000 : ℝ)*X 0 0+(2633980551/5000000000 : ℝ)*X 0 1+(1347564359/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132817301/250000000 : ℝ)*X 1 0+(-1022286181/5000000000 : ℝ)*X 1 1+(5390257063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656346299/5000000000 : ℝ)*X 2 0+(5390256473/10000000000 : ℝ)*X 2 1+(-2044572409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173138381/5000000000 : ℝ)*X 0 0+(4472849943/10000000000 : ℝ)*X 0 1+(2111591359/5000000000 : ℝ)*X 0 2+(2173138381/5000000000 : ℝ)*X 1 0+(4472849943/10000000000 : ℝ)*X 1 1+(2111591359/5000000000 : ℝ)*X 1 2+(2173138381/5000000000 : ℝ)*X 2 0+(4472849943/10000000000 : ℝ)*X 2 1+(2111591359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67267480966887725445491577/18650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11023007/50000000000000 : ℝ)*(base19) + (55206443/50000000000000 : ℝ)*(base23) + (184224877/100000000000000 : ℝ)*(lower2) + (84913111/25000000000000 : ℝ)*(lower4) + (22091821/50000000000000 : ℝ)*(lower5) + (1212067150491883/20000000000000 : ℝ)*(major0) + (1212067150491883/20000000000000 : ℝ)*(major1) + (1212067150491883/20000000000000 : ℝ)*(major2) + (254236337801777/3125000000000 : ℝ)*(sp0) + (8135580227404373/100000000000000 : ℝ)*(sp1) + (8135580139037501/100000000000000 : ℝ)*(sp2) + (1992538525347847/50000000000000 : ℝ)*(sp3) + (8719896761/50000000000000 : ℝ)*(sp4) + (14084544891/100000000000000 : ℝ)*(sp7) + (797018227048117/20000000000000 : ℝ)*(f.failure) + (4067790124725193/50000000000000 : ℝ)*(f.sum) + (508929203319/74600000000000000000000000 : ℝ)*base65 + (1287594549398036141/74600000000000000000000000000000 : ℝ)*base68 + (210289577747363859/74600000000000000000000000000000 : ℝ)*base69 + (350360841460036141/74600000000000000000000000000000 : ℝ)*base72 + (242969752143/74600000000000000000000000 : ℝ)*base74 + (586729435957436141/74600000000000000000000000000000 : ℝ)*base76 + (590166144267036141/74600000000000000000000000000000 : ℝ)*base78 + (2693289727412636141/74600000000000000000000000000000 : ℝ)*base80 + (539168566337/186500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (72313/2000000000000000000000 : ℝ)*base90 + (72313/2000000000000000000000 : ℝ)*base92 + (72313/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7077527034741372506424988179/1305500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61937513/3125000000000 : ℝ)*(base19) + (3501344477/100000000000000 : ℝ)*(base23) + (345538613/100000000000000 : ℝ)*(upper2) + (116276309/25000000000000 : ℝ)*(upper5) + (6091103298149537/100000000000000 : ℝ)*(major0) + (6091103298149537/100000000000000 : ℝ)*(major1) + (6091103298149537/100000000000000 : ℝ)*(major2) + (784850983/100000000000000 : ℝ)*(sp0) + (50428123019/100000000000000 : ℝ)*(sp1) + (26069213817/50000000000000 : ℝ)*(sp2) + (2044220675000167/25000000000000 : ℝ)*(sp4) + (8176831074728217/100000000000000 : ℝ)*(sp5) + (8176827845079541/100000000000000 : ℝ)*(sp6) + (1001330732684227/25000000000000 : ℝ)*(sp7) + (1001330732684227/25000000000000 : ℝ)*(f.failure) + (2044220871212913/25000000000000 : ℝ)*(f.sum) + (32469506182289/13055000000000000000000000000 : ℝ)*base66 + (915111314972995801/373000000000000000000000000000000 : ℝ)*base67 + (2561111164389995801/373000000000000000000000000000000 : ℝ)*base69 + (2323386759950995801/373000000000000000000000000000000 : ℝ)*base71 + (13813395570011/3263750000000000000000000000 : ℝ)*base74 + (2417142098499004199/373000000000000000000000000000000 : ℝ)*base76 + (212713338337995801/373000000000000000000000000000000 : ℝ)*base77 + (1322294126011004199/373000000000000000000000000000000 : ℝ)*base80 + (31063546221957/6527500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (7603103/2500000000000000000000 : ℝ)*base90 + (7603103/2500000000000000000000 : ℝ)*base92 + (7603103/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1274_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (113/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5757/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5759/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1274_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1274_s8_0 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (20875459/39062500 : ℝ)*x 0 + (1053536363/2000000000 : ℝ)*x 1 + (-433429239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20875459/39062500 : ℝ)^2117 ≤ (43759020727949/100000000000000 : ℝ)^1605 := by
    have hnat : (20875459 : ℕ)^2117*100000000000000^1605 ≤ 43759020727949^1605*39062500^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20875459 39062500 43759020727949 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053536363/2000000000 : ℝ)^2117 ≤ (42935378766519/100000000000000 : ℝ)^1605 := by
    have hnat : (1053536363 : ℕ)^2117*100000000000000^1605 ≤ 42935378766519^1605*2000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053536363 2000000000 42935378766519 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433429239/2000000000 : ℝ)^2117 ≤ (1663200062671/12500000000000 : ℝ)^1605 := by
    have hnat : (433429239 : ℕ)^2117*12500000000000^1605 ≤ 1663200062671^1605*2000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433429239 2000000000 1663200062671 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20875459/39062500 : ℝ), (1053536363/2000000000 : ℝ), (-433429239/2000000000 : ℝ)] ![(43759020727949/100000000000000 : ℝ), (42935378766519/100000000000000 : ℝ), (1663200062671/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20875459/39062500 : ℝ)|^2117 ≤ (43759020727949/100000000000000 : ℝ)^1605
        have hw : |(20875459/39062500 : ℝ)|=(20875459/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053536363/2000000000 : ℝ)|^2117 ≤ (42935378766519/100000000000000 : ℝ)^1605
        have hw : |(1053536363/2000000000 : ℝ)|=(1053536363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-433429239/2000000000 : ℝ)|^2117 ≤ (1663200062671/12500000000000 : ℝ)^1605
        have hw : |(-433429239/2000000000 : ℝ)|=(433429239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s8_1 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1052433777/5000000000 : ℝ)*x 0 + (2633996109/5000000000 : ℝ)*x 1 + (2695113623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052433777/5000000000 : ℝ)^2117 ≤ (12803578486941/100000000000000 : ℝ)^1605 := by
    have hnat : (1052433777 : ℕ)^2117*100000000000000^1605 ≤ 12803578486941^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052433777 5000000000 12803578486941 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633996109/5000000000 : ℝ)^2117 ≤ (2683669742789/6250000000000 : ℝ)^1605 := by
    have hnat : (2633996109 : ℕ)^2117*6250000000000^1605 ≤ 2683669742789^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633996109 5000000000 2683669742789 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695113623/5000000000 : ℝ)^2117 ≤ (44257705618391/100000000000000 : ℝ)^1605 := by
    have hnat : (2695113623 : ℕ)^2117*100000000000000^1605 ≤ 44257705618391^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695113623 5000000000 44257705618391 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1052433777/5000000000 : ℝ), (2633996109/5000000000 : ℝ), (2695113623/5000000000 : ℝ)] ![(12803578486941/100000000000000 : ℝ), (2683669742789/6250000000000 : ℝ), (44257705618391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1052433777/5000000000 : ℝ)|^2117 ≤ (12803578486941/100000000000000 : ℝ)^1605
        have hw : |(-1052433777/5000000000 : ℝ)|=(1052433777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633996109/5000000000 : ℝ)|^2117 ≤ (2683669742789/6250000000000 : ℝ)^1605
        have hw : |(2633996109/5000000000 : ℝ)|=(2633996109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695113623/5000000000 : ℝ)|^2117 ≤ (44257705618391/100000000000000 : ℝ)^1605
        have hw : |(2695113623/5000000000 : ℝ)|=(2695113623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s8_2 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312700787/10000000000 : ℝ)*x 0 + (-1022300571/5000000000 : ℝ)*x 1 + (168444601/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312700787/10000000000 : ℝ)^2117 ≤ (21710014049077/50000000000000 : ℝ)^1605 := by
    have hnat : (5312700787 : ℕ)^2117*50000000000000^1605 ≤ 21710014049077^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312700787 10000000000 21710014049077 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022300571/5000000000 : ℝ)^2117 ≤ (2464453284203/20000000000000 : ℝ)^1605 := by
    have hnat : (1022300571 : ℕ)^2117*20000000000000^1605 ≤ 2464453284203^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022300571 5000000000 2464453284203 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168444601/312500000 : ℝ)^2117 ≤ (44257705466771/100000000000000 : ℝ)^1605 := by
    have hnat : (168444601 : ℕ)^2117*100000000000000^1605 ≤ 44257705466771^1605*312500000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168444601 312500000 44257705466771 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312700787/10000000000 : ℝ), (-1022300571/5000000000 : ℝ), (168444601/312500000 : ℝ)] ![(21710014049077/50000000000000 : ℝ), (2464453284203/20000000000000 : ℝ), (44257705466771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312700787/10000000000 : ℝ)|^2117 ≤ (21710014049077/50000000000000 : ℝ)^1605
        have hw : |(5312700787/10000000000 : ℝ)|=(5312700787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1022300571/5000000000 : ℝ)|^2117 ≤ (2464453284203/20000000000000 : ℝ)^1605
        have hw : |(-1022300571/5000000000 : ℝ)|=(1022300571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168444601/312500000 : ℝ)|^2117 ≤ (44257705466771/100000000000000 : ℝ)^1605
        have hw : |(168444601/312500000 : ℝ)|=(168444601/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s8_3 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062540171/2000000000 : ℝ)*x 0 + (2695113593/5000000000 : ℝ)*x 1 + (-255575139/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062540171/2000000000 : ℝ)^2117 ≤ (43420028831197/100000000000000 : ℝ)^1605 := by
    have hnat : (1062540171 : ℕ)^2117*100000000000000^1605 ≤ 43420028831197^1605*2000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062540171 2000000000 43420028831197 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695113593/5000000000 : ℝ)^2117 ≤ (2766106560537/6250000000000 : ℝ)^1605 := by
    have hnat : (2695113593 : ℕ)^2117*6250000000000^1605 ≤ 2766106560537^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695113593 5000000000 2766106560537 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255575139/1250000000 : ℝ)^2117 ≤ (1540283272817/12500000000000 : ℝ)^1605 := by
    have hnat : (255575139 : ℕ)^2117*12500000000000^1605 ≤ 1540283272817^1605*1250000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255575139 1250000000 1540283272817 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062540171/2000000000 : ℝ), (2695113593/5000000000 : ℝ), (-255575139/1250000000 : ℝ)] ![(43420028831197/100000000000000 : ℝ), (2766106560537/6250000000000 : ℝ), (1540283272817/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062540171/2000000000 : ℝ)|^2117 ≤ (43420028831197/100000000000000 : ℝ)^1605
        have hw : |(1062540171/2000000000 : ℝ)|=(1062540171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695113593/5000000000 : ℝ)|^2117 ≤ (2766106560537/6250000000000 : ℝ)^1605
        have hw : |(2695113593/5000000000 : ℝ)|=(2695113593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255575139/1250000000 : ℝ)|^2117 ≤ (1540283272817/12500000000000 : ℝ)^1605
        have hw : |(-255575139/1250000000 : ℝ)|=(255575139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s8_4 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2173139271/5000000000 : ℝ)*x 0 + (4472787691/10000000000 : ℝ)*x 1 + (1055811081/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173139271/5000000000 : ℝ)^2117 ≤ (6663554042791/20000000000000 : ℝ)^1605 := by
    have hnat : (2173139271 : ℕ)^2117*20000000000000^1605 ≤ 6663554042791^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173139271 5000000000 6663554042791 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4472787691/10000000000 : ℝ)^2117 ≤ (34602833908289/100000000000000 : ℝ)^1605 := by
    have hnat : (4472787691 : ℕ)^2117*100000000000000^1605 ≤ 34602833908289^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472787691 10000000000 34602833908289 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055811081/2500000000 : ℝ)^2117 ≤ (32079395867989/100000000000000 : ℝ)^1605 := by
    have hnat : (1055811081 : ℕ)^2117*100000000000000^1605 ≤ 32079395867989^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055811081 2500000000 32079395867989 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173139271/5000000000 : ℝ), (4472787691/10000000000 : ℝ), (1055811081/2500000000 : ℝ)] ![(6663554042791/20000000000000 : ℝ), (34602833908289/100000000000000 : ℝ), (32079395867989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173139271/5000000000 : ℝ)|^2117 ≤ (6663554042791/20000000000000 : ℝ)^1605
        have hw : |(2173139271/5000000000 : ℝ)|=(2173139271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4472787691/10000000000 : ℝ)|^2117 ≤ (34602833908289/100000000000000 : ℝ)^1605
        have hw : |(4472787691/10000000000 : ℝ)|=(4472787691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055811081/2500000000 : ℝ)|^2117 ≤ (32079395867989/100000000000000 : ℝ)^1605
        have hw : |(1055811081/2500000000 : ℝ)|=(1055811081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1274_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5759/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5759/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14121/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5759/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5759/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5759/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5759/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5759/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5759/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5759/50000 : ℝ) ^ (8467/2048 : ℝ) ≤ (1645820685765733/12500000000000000000 : ℝ) := by
    have hpowers : (5759/50000 : ℝ)^8467 ≤ (1645820685765733/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5759 : ℕ)^8467*12500000000000000000^2048 ≤ 1645820685765733^2048*50000^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5759 50000 1645820685765733 12500000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5759/50000 : ℝ)) (X := (1645820685765733/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7061/50000 : ℝ) ^ (8467/2048 : ℝ) ≤ (30579835821440637/100000000000000000000 : ℝ) := by
    have hpowers : (7061/50000 : ℝ)^8467 ≤ (30579835821440637/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7061 : ℕ)^8467*100000000000000000000^2048 ≤ 30579835821440637^2048*50000^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7061 50000 30579835821440637 100000000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7061/50000 : ℝ)) (X := (30579835821440637/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251645820685765733/6250000000000000000 : ℝ) ≤ (625039805177331/625000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (6251645820685765733/6250000000000000000 : ℝ)^2048 ≤ (625039805177331/625000000000000 : ℝ)^8467 := by
      have hnat : (6251645820685765733 : ℕ)^2048*625000000000000^8467 ≤ 625039805177331^8467*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251645820685765733 6250000000000000000 625039805177331 625000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625039805177331/625000000000000 : ℝ)) (X := (6251645820685765733/6250000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043746401307566501/100000000000000000000 : ℝ) ≤ (2500264490896961/2500000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (100043746401307566501/100000000000000000000 : ℝ)^2048 ≤ (2500264490896961/2500000000000000 : ℝ)^8467 := by
      have hnat : (100043746401307566501 : ℕ)^2048*2500000000000000^8467 ≤ 2500264490896961^8467*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043746401307566501 100000000000000000000 2500264490896961 2500000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500264490896961/2500000000000000 : ℝ)) (X := (100043746401307566501/100000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030579835821440637/50000000000000000000 : ℝ) ≤ (1250184880542299/1250000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (50030579835821440637/50000000000000000000 : ℝ)^2048 ≤ (1250184880542299/1250000000000000 : ℝ)^8467 := by
      have hnat : (50030579835821440637 : ℕ)^2048*1250000000000000^8467 ≤ 1250184880542299^8467*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030579835821440637 50000000000000000000 1250184880542299 1250000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250184880542299/1250000000000000 : ℝ)) (X := (50030579835821440637/50000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1645820685765733/12500000000000000000 : ℝ) ≤ ((1626997401671168441/1627500000000000000 : ℝ)+2*(105270187637/65100000000000 : ℝ)*(5759/50000 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (1626997401671168441/1627500000000000000 : ℝ)+2*(105270187637/65100000000000 : ℝ)*(5759/50000 : ℝ)=(625039805177331/625000000000000 : ℝ) by norm_num, show 1+2*(1645820685765733/12500000000000000000 : ℝ)=(6251645820685765733/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30579835821440637/100000000000000000000 : ℝ)+(1645820685765733/12500000000000000000 : ℝ) ≤ ((1626997401671168441/1627500000000000000 : ℝ)+(105270187637/65100000000000 : ℝ)*((7061/50000 : ℝ)+(5759/50000 : ℝ)))^(8467/2048 : ℝ) := by
    rw [show (1626997401671168441/1627500000000000000 : ℝ)+(105270187637/65100000000000 : ℝ)*((7061/50000 : ℝ)+(5759/50000 : ℝ))=(2500264490896961/2500000000000000 : ℝ) by norm_num, show 1+(30579835821440637/100000000000000000000 : ℝ)+(1645820685765733/12500000000000000000 : ℝ)=(100043746401307566501/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30579835821440637/100000000000000000000 : ℝ) ≤ ((1626997401671168441/1627500000000000000 : ℝ)+2*(105270187637/65100000000000 : ℝ)*(7061/50000 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (1626997401671168441/1627500000000000000 : ℝ)+2*(105270187637/65100000000000 : ℝ)*(7061/50000 : ℝ)=(1250184880542299/1250000000000000 : ℝ) by norm_num, show 1+2*(30579835821440637/100000000000000000000 : ℝ)=(50030579835821440637/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1626997401671168441/1627500000000000000 : ℝ)*(X 1 0+X 2 0)+(105270187637/65100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (5759/50000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (1626997401671168441/1627500000000000000 : ℝ)) (alpha := (105270187637/65100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1626997401671168441/1627500000000000000 : ℝ)*(X 0 1+X 2 1)+(105270187637/65100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (5759/50000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (1626997401671168441/1627500000000000000 : ℝ)) (alpha := (105270187637/65100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1626997401671168441/1627500000000000000 : ℝ)*(X 0 2+X 1 2)+(105270187637/65100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (5759/50000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (1626997401671168441/1627500000000000000 : ℝ)) (alpha := (105270187637/65100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((20875459/39062500 : ℝ)*X 2 0+(1053536363/2000000000 : ℝ)*X 2 1+(-433429239/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1052433777/5000000000 : ℝ)*X 0 0+(2633996109/5000000000 : ℝ)*X 0 1+(2695113623/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312700787/10000000000 : ℝ)*X 1 0+(-1022300571/5000000000 : ℝ)*X 1 1+(168444601/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1062540171/2000000000 : ℝ)*X 2 0+(2695113593/5000000000 : ℝ)*X 2 1+(-255575139/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2173139271/5000000000 : ℝ)*X 0 0+(4472787691/10000000000 : ℝ)*X 0 1+(1055811081/2500000000 : ℝ)*X 0 2+(2173139271/5000000000 : ℝ)*X 1 0+(4472787691/10000000000 : ℝ)*X 1 1+(1055811081/2500000000 : ℝ)*X 1 2+(2173139271/5000000000 : ℝ)*X 2 0+(4472787691/10000000000 : ℝ)*X 2 1+(1055811081/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (137504579427830650481003211/27125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69186797/6250000000000 : ℝ)*(base19) + (666448369/50000000000000 : ℝ)*(base23) + (161257239/50000000000000 : ℝ)*(lower1) + (1858663/4000000000000 : ℝ)*(upper2) + (176328871/100000000000000 : ℝ)*(upper3) + (165694401/100000000000000 : ℝ)*(upper5) + (6094120624992971/100000000000000 : ℝ)*(major0) + (6094120624992971/100000000000000 : ℝ)*(major1) + (6094120624992971/100000000000000 : ℝ)*(major2) + (1140875031/20000000000000 : ℝ)*(sp0) + (8180934048574741/100000000000000 : ℝ)*(sp1) + (8180932941585989/100000000000000 : ℝ)*(sp2) + (8180927011302849/100000000000000 : ℝ)*(sp3) + (4007307032434741/100000000000000 : ℝ)*(sp4) + (4007307032434741/100000000000000 : ℝ)*(f.failure) + (8180934048574741/100000000000000 : ℝ)*(f.sum) + (21167283622013/3255000000000000000000000000 : ℝ)*base66 + (1262983200634546789/162750000000000000000000000000000 : ℝ)*base68 + (8648766065502703211/162750000000000000000000000000000 : ℝ)*base69 + (1153739280583546789/162750000000000000000000000000000 : ℝ)*base72 + (349589118211/406875000000000000000000000 : ℝ)*base74 + (2664145986887203211/162750000000000000000000000000000 : ℝ)*base75 + (661579321201546789/162750000000000000000000000000000 : ℝ)*base78 + (3917597425472296789/162750000000000000000000000000000 : ℝ)*base80 + (71385505279961/1627500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (18694649/10000000000000000000000 : ℝ)*base90 + (18694649/10000000000000000000000 : ℝ)*base92 + (18694649/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1274_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5759/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5759/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1274_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1274_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (442/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5759/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1274_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1274_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1274_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (442/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5759/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1274_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
